-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:38:31.831926+00:00
-- url     : https://prove2.me/submissions/5c1a2406-d890-4373-8384-d701ab691299

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 741366906 ≤ n < 741546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 741368156 1250 741366906 741366917
    0xa170309010209060f0a0206060a0b121f0b0c070602010b1f03180b0f0708010f0303080c1905040617040b070f1e020c0f04090b130c0506031303030e010e0d 68
    0x1110060329009101d03000076560009004140303c0d92000c0d400015100d00b00540d020f64a0590b20030381000f003207455500803100d2004042c0121600700890b10099680000c400e07a00415040d1060908900e800301c6c5d510401c040e203000500c0402c25082403049034000c0840303000a10203003040c0f80010703004203910400043d446650401c00c8040d18400d800c8400703410340c10708100f00000300504111100b0681110490082401030021424042c07141c0c84090485421812000710301c2d06554084804c404003800680f0303540710034000c1610502c40001419044107185e00c1e440d5880d4607040e0090701a040b801840d40d42d603c1c10b04100b001094006000b0362b4172903007500c1c2035880e4551814050b22089103c4118600314031000c2c2240009580001700b050b14990101c400c030f072800341c08030704000950305080e070003c0441055801140350f84e01c004d60b10905413407180602500340d03521000810030f2500100c1e00342603000381d686585420705406104030007014000e00f0003441f45000001c0169900c1d04050400c504104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 741369406 1250 741368156 741368161
    0x21c05030415140f01030b07020a15090c180501060f02010902010906080619091d03090319050307080d050703060915050609010e06130602010b03190809060c1006170a1703 75
    0x980c0d803110925090203c8840c160342044800002011001d001c21a480140b540c041000f0900000706503403002d6100080d00e8600c10f640440344054245404212118440080c01098040142800a0325200b01880c0040c09602d0001e0040c0280102420401036926210301000540d0f17001d0302802c1910498108003d4a0301d030b000111745080000501c0b0a04e24011120101b810300540d0400c403050010510043c441003d0080c545881c0d100f003591155060303020391902c213802d000c4111581c015034000c0341981d0815549403610000e65225a92005105940c1d0080114864042c07003000d001d020702180400034007280070042c0d8420300b040e00400344954000304008403c1d80c4120150422100094403054540401e07158900f07041405008041c00741d420304030f80c02024200001c06505504d03031906101307080303103060300d4101c82e55200c801802c0e0803607410400343c2e2036102d08000061100d03400c414006001850440b8025140c01c260f512003420b50403807240107011820003032108207a1001c0c03001699494 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 741370656 1250 741369406 741369443
    0x150e2505042106060618050d050102091804060c0903050a030e030c12150c12011404091208090c010527040204080105070f090902030115030203100e0c0703021c050304 73
    0x3405039a01035124800c0ba81c955a403079a40d00c0303a02d0100244a402e09000540c4c0f01c440580d03d03c891182e02240710120b02c8401c0000b46454007107000700f00d026200061a000c91072004c80d6841d0382001c11080d088400d08140010080c1034412044128203514203c600281195034540c1c544044041c058100110040701c2c5460395800d0003050703082e01c070040c80703040c0101204040c10b4454510f6041704e26084802000034401020b001d0407601920110302070703003100e41e090010820110542210071a00b085d1b0368400c0c6400640d000c2da24030001262510703605002c1c43d02000aa2030f00101e641080e040203000d1220381110b07801c103248140a480031500d440002200000814028029640b00345819820502403045460b00500c0d0b03280070204030b0351404800d94454540d03c069100a1040003c600109098018018400c0c3e01a507000035540724060901590f501490000b038005540041d02c080e000122001010307010040c0d0407641c580d001c900c07005103131032103005003d500000300007620082101c942403441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 741371906 1250 741370656 741370667
    0x120f051002120705071b090e0606030a08070f0501090c030807050c0117060f03031201060509030f0d020a020108040f0b04050304090b040b090f07020a050304060e10050c0d11010f0609150e25 83
    0x2001c07041d03180071496907070380c41f038120280160054907100c3e40268804181c09081c00b00d60404082e8124807020b14101182e66501c0811050000a842c2035584074035042c0011960684c4000840c0a940d02e1a00d605840c14140d042085001040d8140161f5070000d13218262048040b07a0b00281c111503d10540a0800101e82188100350450580008100011508a0704803004c0e2010540c190101c442d100e249603041e41d038a001000e00380025078070034403e100056201e041007070343c810710601c40601a041d0729541c110404009135411070b8240c10110b03080c00003640d9031003581d0944208940600c00904007401281c00c042d00030b0b1841d2864003c040024685500130401ea030b41440e4080c0c12250b942c0e907035200044c150001d080a9900c55119060340a02c0c00d80b1610541d503142c60140d0107000091a0300509032542c070b4000c0442d00d00e1755211420b00d846040302e8230401004240480700840d03244040b010140309104141c00c94005401150103000141c1071564608510941404040c2d50b403200c003000a035103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 741373156 1250 741371906 741371933
    0x1b061606090c08070506120f06011e030c02010b150415050f121f080d0c060605030106060201050105120a0c030314070209070203070203060a1802010c020a120f05100212070507 77
    0x3018200031003101000788a4a80300202c0b03610005564113142c881040110320b00c11504010340103610075001ca21100000030b41150040814101380c0d500c0580b4002d214007a000041d90000840d9441c41909041e070340a00a4071442081101d01c40004c008a0000840381c1c0118060312200103015180e40ea071550241c0c0840d951854611031254580110307845502c024601246c00c100b0b086c110407a4100b500314031200141c03e540008001e0030125110510403070300412607030300507146035440b1500020661030a116207005403d155002048944c100014440c00e1440d81c01c80000550120460f00081112050808103481d0305160200d00f2843d06406c1c0c1030b06009412000c5d600084080a00032100d0b0000010801c0074425410707038041e0b44d180481081101c01382d2941c00d451402d1000d201c40150f00c904084104944000c10221440f601c900344410b5061200070100c48115070034040718103205040025131a41102174005524240640b4078049090350040d080c00184403010400e10100218030a2214 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 741374406 1250 741373156 741373163
    0x10f0b030613060b180301092f06040f05040e0a020906240a2609120f040806010b0406120b0d082107051321032f0c040b031b0616 57
    0x700da107841c0d1881c800c0c29801000303000100c112243e00d03000c660030180100541640c21044494240d079032440081c0004100c204031589c0f0030803070040c08110359a24400760002c2c006071f100000c5414101011700003201c00001c0004942d900c144070010044e500e12646a51015064601311201c000b0360b414040c2700301c0320806008040e400884c6002c840b80d880f6000d00d20000300b2401607411a251070f5681c4200c501d017622414100c0e001200041d000e4591000142040c04001c1c400360318180d40c039250542012003e822130444440005410030150b54442c6801d500e20403406420400314040c1b0380082d6022114003401450745038046480b0b85400640b10b08000d18141c240302942942c03400c03070802000c03984295807411983d107030341201183c852051556424070b200050b06401c4981038944040e200c102520403450b80440ea41200f0b883c0346c0020403200c1d50154444401002604103034010842134071008501280240c0c014001c0c0740c0d2040c586208252641c10548043c0d1350707003c0501400c00c007a00d0707070300700903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 741375656 1250 741374406 741374411
    0x90a080d0206150111150603030903010603050109020f010203040e0a0917030906010e0c041d0a0e0a0309030515090a0311032a010b0405041a0703060312180b03010f0b030613 76
    0xc05200e40120b90b8a105101a40c01921210490700042d128140b1080c0b40d0011036000805c40d160171004404060b800c140014116410803400d4800a400e643c201d0300308540e03d1b51164a40d40c11030820346009400d0801c00d001440c1864184102401480f400900c89580d03661200042d8050082c2c1c041d6030a07003490400780b80755a82c50a0b1601a80d542c01c00e100e50660068044000703217131080342d80282c4040d500d0060020001240c5d031031100314030603009400804844e903580418140309104100800b00140300751501400e061641c1015030501c0b0324411590a40002c1e08100040000046520200a88c1c10b04160008551640f4054654010b100d01442860703030000704040045100c2d4030816101c00c108000303005000890080c0401c1d46c5056600a00740c51082c1100c81f12404925009030307100c401450001403103a0b49403100c90080a0241410001c22604c0e0002d250902000316807a0140110064051640d454840d102c01062a14419900f4014012002c03c00998031500b080e03441c0001d4005c02d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 741376906 1250 741375656 741375673
    0x60c05062d0406020a0f0509030d030207020a050409030903140c0a06050d1b021b04090c0e0a0905010221130809011809050a14070c150c020c130506120a0b040602090a08 74
    0x148000394440034440c0d001c9052541c081b011079104600315415000d025020303110810940390140c02a40200348103e034800d80841d80801c140e00c0f907100d6581c45a009a0b610031803149541494140d1401d86618101c2e990040b40c0131100d41e031a060680d0303046a4161400da561035003101004070003007682104002d03440340715003401c0d84000d41c005007040104010760800404c20303a28004010440c0c62800c1c004080041150007081611110345900340d00c8003c107000030903200441c1d0782e45400ca902200204070840b1032100031004081401c21072a900241d03c51520f000c115041c3c40e100c88901030f000a43d41040001c0580a500c91205280c03a401080c031007909100c03d04180c040b260180c02440401054a843d440004441c244a104040f10040e00600d0848070001d03851052070240114141100c00c1d4400c040c0c030b11025440d2a1880301010009000004d201e0620304108040510b0111680e105948100342002c085100e1001c603d800c0b40d808000142d56051080104052041a500194040c09600034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 741378156 1250 741376906 741376913
    0x311040b1207081029010c05070e10050d020f0603060a1a030106030e2b0c05030a0806040b0a0501021e010e1606031b1d030c060c16060c05062d04 64
    0x1031080503160703818152400010885554021a04e100e40311750081007409034070010b181005042249104010302d00104e0440c17154a40da4548052a400b007404060310104114100c14145a000041c1c44219003140200e4416000900074080c4c50041c60301c60700c000804038507542d40e804c0d2910010494000c60305001c601700c1c601c0c00019002441080c0200703082588200c080d41d00805c031b000303451920040c03024032810040c0c4801c3d5108521450142804203501040000c50f1041000c0c05443c030041c1c0d00da1146190800c103110a55041034003003402241e84000c148a16038012402d0780341002c1440d02000000540170b0003a01400c203030b0019110070b0140b0142425105614907020080d1801a11b00740100301c900c1d19a2003003000c0102c0060000341d9035440c10040030510a109030080341008040b12400c011100008115030b1002c031182550b588100041100d241d0340c0c01c2164014031031420011a000e225484a0392a804010103a43e2048031481044007913000e0301001040303400d403107248800c0b240f42c58134 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 741379406 1250 741378156 741378163
    0xa1e090c08060a0203240d061404140d050403141c020a050105060a0b0f1305040f0e0714180703020717090108060904240905012f130311040b12 63
    0xc0035958020080040e00e1201035000301c90141141c1e160040c0c0310703032080304086e00805a0318245944488654014408100319000c2c2c0c5100500c010305400700750074a03281c01c41c5440320201d4480d429402c00d58900e034000e6082030a440859800407034003440c0c42a00e08006007028448003140c0000c2020200801d08142c0c006460710415101d10000c01480e201c2c44104040d0a42078860100d00c80301c00c10844000040d0b80f0050881c84c0e0240d03a01d0011561603000142c191000089544030f1a80e44d01caa0691b2200100098401000c810910010709540342001c2801d00202c00054080410074034081a160744c0310340d04449a4540100c00308103014000c45803000c0ac0c0d48004074290008454201040d42c80c030f440c1003201e0195038001c000110000c450343c802c015030015100d15425040d513805511001c1842806801c4042c083ea821407014071310005d900300402c80586100c000d54480610440700a15190038421040c0d0360820410502c50740c1c034200043c05803007035821f82504242c010300e06210650001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 741380656 1250 741379406 741379409
    0x18010b070c08030301150c230303162a080c01020310051503270109080d060303080106020f153102010e0f0d3806010e10080a1e090c 58
    0x9002202003641e0302c02d100ea590f80800e01602101e440e40d280d0419059000f0484840c0c0607204403401c44102909154100400a00d00103850003900000104045120681c0100300140d0590400030385514101c00c09000e11031070f0551102c00003140200305000e008036901628412a4814000e540d2880c080c10401c0c0300b121540308541c040d100c00c1c0d41086410900506591185407100020380b0407100401a02e91040b400080b180104e560321140d48000c00c01c0103000780fa91580100010170403515600e8020300d200c005070b2007230045411403070010303503c140701088900c2e603920f846005400710b403150b5041050b4040304009950060404172005001070b0341503550321b900035000740c96400b00310407074200348030301c00100002955100204800b80400556406005041248092072649440c1c001910080304084015010b02258003108100f0480f580c1c131550421060340180d4100560844091015000c01d5000d80301d1001b0701c0c0c0385e0b150350000000d204c500351428010701200f07015008030b60800d04540b4829 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 741381906 1250 741380656 741380663
    0x140414070f12110a050105030601180506040603021c0509060f0406110307180e0105060d020706021605030c011503080409020c101d0105010b07020d02010507140114060f09160e18010b07 81
    0x1907203c4030070354500741100e2811514181c5803103203075556400044852794641d80e100700d450b206142d00414240c9030303c8081c101421182c4c60040c1e03114221404a0380e11900b0140e6003212a0615080003d601c1c00410001d030812001100c101003a00c462406001900104424a6101d00c1c04410040010707801004800010ba00b454540c401e29200c00c03804450a8090040a030422030030004c0c05200d0803a50300905a0034098280141058010f01c2e0314070034030310247d400b601c9560000c29403041855003849182c2c04c0f200d404119a145500d5555905628000c511070200030713a0b804544111410b100b8000d46901d40e1501034104545035000e01c0050b084500b0800d5607075150328100000c183c215100303084038143c40d001440703415040ca141c0d00445559000900480e004d0741c0780a148000341d5024014115a803e000e003040b135192819805000c00301c048100308520906195050110102045c500400405081d10b00341d02d0150010000c01c0050103081e286c50040203a0000002c2d501121030040c040c0c0511 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 741383156 1250 741381906 741381923
    0x32150403080708011401050f13030b061504030b060105030411120f0106050d080d0213090509011d1903081005061206090c041505030a11030406090302060901140414070f12 75
    0x40b40c40044850000c240240038a100300f0442c000344c1c641c041d41c05443d80b003501e40e000c030f80380c03400c05499800355a405500845181ca142d400b0f0060f14544042c500d004101c42180f0241418039544685034079200103803405061000c0080407a05102c2010b19951080e00f000d440d030101c101200c06d2055440b2400c4103092aa546000404601442e000c0500d600003a000010642032a145100ca03100030350202078840e4040c9002e00c800152050540192481404840000a5020a80171504c450803411000c10381d03494104061410403250f10750004034000c1c0d01458414001e944900031203940b194941c0160758000702c0070810184466205a542d441400181c0700704160b522501c1409030310340258020295010846041044d095101e031014550281401c0e0000c82c40d6008403c2150190303100780c60a03580248c03204911b1040c141c041250f036400102d590f0082026951784031154404800141000b00200817451900615030300812100014115048000c038810355202400603007001c032001c04071503424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 741384406 1250 741383156 741383161
    0xe06040c140102060a0c050c0d0507030306060f0c0b06010207050418050c030c130e03270103060b04120303050a0b03030c0a0b0906040c1206060b03010603020909133215040308 77
    0x703819040703980301d406030010107964a0b105c964002620003090440108107040c08004080e010420040341d05200540751590341e05611704004054030600c0d0040c0060003400005115541e40c45000441c0454002045803016120040100d040c40c01c2c0d0341c0710342e034401d040501a010204092007061507191080c4c080b12008010b1105240c3c60b8405a0311680d031007140780161100c5560740750420b0b040c000010341940d20b041134402200c20030300300d0044138040701540f16100048079609842050007610315080c0c1c40c2d00345031600030804140b048080004003050788590102d0315070442c0f5002151800e4005081e00e44414030948016a62031041409403055024034000c0b5003990004900302c0d00440e0030120342e01e01e140c00d00354114080e071104c210461f50030b0361b03542c80010028040f001440c041e2a880d035015a4801d50001003151000028201014141070301513100d00044035403258106e068140409044001c0124030035031849029250201031034007600c0102000d440c8100c036403500c142d2007030300c0d000c080d178 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 741385656 1250 741384406 741384419
    0x302040f0509070f0507140a0303020c0c010c08160510092d05031204030e030a050c010f0e09040b1308040b0d0c11060106050c12041514030403020c01030b12010e06040c 74
    0x1141600c9003408968602030328505103205d00018100c4500695140d0b00d143d01a03142c4501d010b00000e01a800030342e000c150190040c42c1485443c10100c82440c00d041024040d4031040d0041c490401034000071002e0031000820007400b4001c0d1004094164401c00c8664118200032104418000300ca41e58018040c05e16a80140c44038001c4504a400c80300460038005960380804601c10094400d40034401480c013000e002da6001c00c4201c00c0540f049000e0301206070b00c04005040044c10040301c0c02032080a03130035070b0b90744d4654020355503010f90000814103440d01c0e40021b00c0c200360001203000d841c03040c00140200c0c0441415004010000001030200040d202800c030450311052103036616100c6400000041014501c580003070004940300a0982c4c180d640c400100540c0347d070190784030a0b41c5607920b03040800d4003500300440281070400e24603c0c2e8a1072415503002526410002040e5052550310401d074000354840d50340010000344d20000800960002100e490740d541030440341103400200400d07012520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 741386906 1250 741385656 741385669
    0x16030207051e090a06090513020a0f053f06041a16080c0d020a0305010f1a0f03190e0a020f030102090307060503040213050705030a0509030f0304020118150302040f05 73
    0x30142c1c0c00420b0034440c1107801c0242d00314000d80000600c5841d4140410100c800d0302c1550700412132030b02600b5804c0d0040c4103016505545900c5210308540030075003004140c546180546403404000040781810342d441199508400012079a081d54028850f0385070b074506000a8210b0090380100099110010f01e120480400724045540841c0c482c544010700205030301442d10b00390040e0b040404141000103d905c000100d17002030341c0500c0041c2e142c030010012921210440e5026122500310082c0340300590721906864824022050059074002001500c006408100040c8502c0c04000900c44010520891a41c0c0d12251313806030b10980842006180c903203414800c4580390b44d03019001d81b8031146803000c01d54080d0401802079802400111650358003500d1481605d20884140c0c036110740368204840000125000244050210752041203244031300421201a00c2e4810790910307024074600c400c140701010300d074860783c066007011618031094090f10350150050320039582c0311a044c5426070740c2c4000308030b034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 741388156 1250 741386906 741386929
    0xc1805090111120727030b01080c0306180a060c030f0b040903210e0607050c1b181801050c0a14040b0d0e0f03030405340b0c0f031603020705 62
    0x4584000b008940c045060034801e83e41d1010b1307103041c69842070b504e00f20301141d16420382040610b10a0001c81c144104211031540b140507204940003070484100090200395106009010185800d5001c414507803021410000340308203d920034403c0c04858016500507014049a440f09a40e20742002614002030070507206407400b041d05070fa200e0b1420359020401190140b0b00814882d4055211114032200c04020462540203a845035036840c1da170103003140c40501b1300346644c444030002c12100c0100421940c0e403a48200060021017141201074513100307868250300050800c3d0b082694285030420007100000380213011082c14903103032480a11b514407000c43d054482e5005400040d28140401c0c01607014950140300301340c4281045400300840e90f50001e14507001105c0403201944100100001c001c0442c1c015100f003603908000e051180c2c0f0700301018803116960301500e600800701144c1080700e5942046040455209c00090740e070f1720554009403000001c50075500b50058422800c000680d07062550f41c140c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741389406 1250 741388156 741388181
    0x90c0c03080a0e010e030c070501180806010513020c01090501050f0a090302100b040204050d0b010906151b210e1f0c080703050f03070503150103050c090118030c18050901 75
    0x741954595407031000800000c41024415035a910b143c0140000c204001e001c110724810007400110b00d02000186010701d804c0b17054480901c40300d07042094140009a140c15542d045174103034244c0c0040100c0200a004a0346241155802d0030045824881f065100600490076210090345540d81c5500c220190b030034601000b40140d000e03020b40761590f00e8a80c4540a01100180f01614003030ba19000100207484150781500e442000d0f40040008040303900c10303200105500208100c0c3c1c1c0c0c070110740203800e03581d80301411009040d410b0b05010402c0301d0140038400d0305c00e004507800103044020300000c0100014010702ca01551250b1480040031100746c855032240b410a590340c40030b859203507441006980000c18220240001800700300c0c1c07001711010140d0310600032582d1b0319441e860644d0780900b804070004031043c1410318220900110181450845800c40d400303081c1f80103001d82c0304101c0021403829a00251400191034000f0818511034030207030240940042040c040c54842aa05508036500900c207103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 741390656 1250 741389406 741389417
    0xb040e0c091c060b1c03141905130f060f051c0e07031b12240501090507021b0901090b0a09090b160206010b0304020d080d050907091a1c1e030207090c0c03 68
    0x40000340b0a01d40402c1c0c1c0590510b1050130052924025891007100c86403040c040b41c8003203140804118041d04100082c00e004100590380cd20705480901151441e490f0042001000034980d000c030342425040b00c284410980c020030806403d082c0a98441216000403250130304c03250351401981c03988002c000e0a598620080300241102c6a4076034900d051000034000d92105c50091035070f0114281c1c85854020300300031002290629100f1002800d01403143c0c3e0020800c040400c000c03806031a00000345040d240307444000180701d0311a2000138600041a4802c18203c4d060042100c100020005000d011f422460700c4102e010200e180c0c107986a140902400d07580e550b013440000d000d0f251103d00a20000d0092107051301c0d041200010405a8100303e070002c100b5440341ca010000081310b03114980d8601c00000e00c0c0341207103500d1400103090440501400d001d08400d20608000c1c0724000001d42c00c6071017906031900080c0302a19000c0c0d2581282d02c511042686400406821035010f14070207070303036036034581e030398 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 741391906 1250 741390656 741390709
    0xe12030f07140a110f041b0e030c1302280c1704050405130309140a050d1a0703050f06040b090412140c0a1202070b040e0c091c060b 58
    0x105100381c001440036203000410706603100001e0070074402d00c0c01e42030142205014201c101804c1c051003486100d6418007507407421540c10402c48135907640c0ea0310410b80d0b1500b5145600b030742000074a03044440c8440f0303034080d0030004400180c0c1c60f99030080114000000a0f007010200c059811558071074810a00408600c01210180028040f69403944514001103030540c200340e1074001140c11a4000c036005155200c039111224185038000245000804610f07990070202c010600218030301101611030780303004070074617220001004007080c5801542c1600300b00c81c000b0380c685168003c01900d0169040300b0441600c0c000b041260503e4000c81342c41c104042c180008545865039a661004e4807102014104007500f95031000900e410801017420004581c02480700c041c06051490603c0c849040e0842990f11004040100c6101f0405803011603241d940c0c04602c564410a000305184075911809502086000b1400780c550010b002040ea45806110108034002d2346400f130042c000b50f200d0003100e00d840070f95072 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 741393156 1250 741391906 741391927
    0x405150a0203120c1309020307081807060503130515070e0a061403100302060307020c091e0103260d0c08070206070e0d11040e0312090c0a030809010e0d050309010e1203 74
    0x1c0f038a8201d102c0f824590328000140303005051a011540180c11541d03000030901c12444d5001c940a034201c3e0745900381c2c1d01c02c510480155640c0e014548900c0062101c04030007d41d50100c15106e11803502d41090566960800840750b0341d50710341c02102c1070f0380840c0b5000042d48240c10303e540030303509943c2151100301c10001c00d1108000c031904005c050500c1e0103100000800182c03159030103940215115002001c0c0f0300b410b041084082900100144c421400070007941d041c0e03a0080580ba4110394104140035040ca1102c0d8100800403005090340036809400079841c240030003a684180c4039981c040d03441e419251180041240c5640c0c1c29100c00f07000429286a100251900e8403c030382607540b26058428226241c400490169031074050000c4403500041007008400000da0b100540c020358080162411204081c0060209000d5001c09000c078180071034050403d90103240100c69030003004094030781c441c540340780641c1d907980054a007600081e04032500c00342d42d04100550300001d20225000e141007407034a00c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 741394406 1250 741393156 741393187
    0x2120306030109050a0b01170c0f01050a0c050a031e0e0102100e01022506050903030f0f0604110712020c0604060c020d020307120f06060608041104110c01060b0405150a0203 76
    0x40035030354955030b640f01150020f8420800007180c10b204030054556585422021000085110031071402508404402c0010b0b580742401d01d1025802401c00c29208c54030100b0449480342d05101c010f01c10300c40d80d24804149900114a0450810000c940000d119035901040f0b275118107049140340568040420035a071440540c22002050301e5540006003043c1100750310704580203503410044400c096800340003003445220300a0070f0f44021200d00662035030512017a00c150004000340907468000400c0089149507a60350485114015a034100c10346814081c1070403801c90407030303032001c04c00351003961000804c03410100d060700c0c1113820607210b00b0241000c1707030244a9104844101242d25004101c00440c2c0b400d15190014280c84c003130a80b401030340117585070100072500c040e001030050101c034108100001e007001a200511090681300820380c3c2d40e10010ba80f4186c0504190b40195508005c80850550000e0000d8000c0340d804481d488100802110a000780d4420401c00500607041080862414040780 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 741395656 1250 741394406 741394411
    0x1505153f011404020a06080702060a020d1b121a010e041e020309031b0c0a1203020114090f120304080a181a07030e0901051f021501030c030309060807021203 69
    0xe4040c40c400060316400300d007181c620008031103410000038144019030404002e036201a04860420803818100300d00082d59444001740101d10072600018402e46440340fa070480d0054041d2242c003000c0003149540003404024045000d032031458540301401c0310704400740c02503100c8a88182c48000c071400b03400c81840007070004a14103001100b003500c0036072031b021010301c000c51007111500f02454881e074420300c04244000000b101c042c05940010303a0307803030340e82d0310584d2160484161642c1c52200300380c140f0f404ea01400d1380c00c02034552003178010200b081d41540462800c11542d40c0c0d006450321b1340c00d5801d00303000c240416940901000010b00c0125241e43c0100403d08010300120303e0301c0741e015035032084190200803c9400c2c00b0001004a00c0c00101500241d461386091000c850744841d560519010a186039503203000c048090320700c1d50001070124000d0204525900410010328103c0d038407400e014410000501c0304a000450720310000809900c1600c21a016140c00d40c0986020001ca405102098001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 741396906 1250 741395656 741395749
    0x1080906040c0605070807051c020d09060207090b1f03021c0e0a1b0b03010617090109020f0402160602220b0c190c0801022a010c05030c16150515 64
    0x40000002148c4100807009813082c41d4030400c04034518040d402801c02c103c02c03003030205000e400901070200c0b507008290070007a073701e02c0391000483c038011900191189107458110b046110320134940f529a1903040e00100141c2c0d401141240c06840401e1690701141ca0204003400302741c0041d1541000540c0b1011030700d41c0350086220004102e52144110081940281d001d00046066154041e06401505038015404136084000b00034000090300400c04440c1c803652079511440c0e00083c0d03c11204540e4035500b16254015108540382c01005081004440c0d18031705000508001d88000240513900c0c0c41100d0803000510b01030940c40000324401100100e4149084942c1c40d5900c0002c40c039203030700f48040c20004012102e40e203001d01001d03080b01000d901c0d050403070380c2070790506071440c84264110301280d401140700d5038440c7e80c80494180540440c24180b00003056003103601e050b441c0d28440340d04403500070789040485008444616003000360250f6845075112400708180ba03440e0b0480074412105040942 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 741398156 1250 741396906 741396923
    0x14060f0d06180902030c041e0c031104180b100914031903080709051203040b1c1e06050a0311010318080301080a140102040f051315030b0601080906040c060507 70
    0x8845285010311400d074448078001a0703640c80f04006605d403c221035801d6203c00c1d03c00b00031100c010080c0c542c011000300d1492841c245c8940c03442d00141e2003071b40311580144003030034035640310358461904210400e01c805081c5059410000f5000151a1404a402d0245010f0300c8080380240ba000d003402c2c040c3c41a100b0580e03d07020380d101c0354000c0403000b4a403020b414030035600c0f5549c1d440d1690020342a0440d07500b2249c001c1d41e4014840301c00c0340000084906683d00207080c030b52102c403980d0000c8503c0007001c40080f40c40341400e00002860410a8201044102000b424480c041d180c3c4180801010b40c1d00c0003801e8150070028405007940654001c405035014503245e0b50003112141c079224440d60003a40100d409510003560030041c0451103c0c01d200c0b14074200c009501c0c1601e410700d1440c0c2d62480e0b00416100340c0250003480124134050740401001c000110500549950380d0500302100700b81284c00c4c90108840c00d0006010032000704500d0b00c0741c0d0b4051242c1404038103003401110540c000c0d103000c0b1011038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 741399406 1250 741398156 741398159
    0x906080a2a090f0e06010311130b15190507020f060a1709032a030a0f050403200a0501020d3203191103090d12020712031514060f0d06 59
    0x10701140d11001c1d000242c00402c0e0751451a10400c00c5480080300c0c501560031820040c800a50100404542001c04881d003c81800c2c00c42c111074028400f0f005000d50200036a03100117010320b03400c3e018080c1a9003845052501208079042a0346034400c040000b503010b0706580d1b811450b40350001c042c14181e141c0d45040f81400e0028003400500c4001503800503007982c170105000f080c64040081a40c002c0e159010050b0080985400141d0f481c050701c859101800055442c80107000d00c1a03080d40c00658001e001158140f65030041c0c4040019503400c0c0c503025407a03007203010035294000104000707045032a80c4d03454810180c0086120310500703c41510a0044010000c1c2110112104081d5000f03c07090f440501101441e10825001c032002d40003045e07500b1409004000d9038800101d008040b40240f818100c20036060118954020311070031100904019425000c0301c41386038540e002040c4111a03820703501240e0b4607400a09051200c03a41c01c507070711810401000160390b10035000352003000141b00c0c0100d50079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 741400656 1250 741399406 741399473
    0x1202070804090911030c0a1a0f19030603030e06030405150a02040506071103070906120b07020312040b04050d031a010e0a050909031c0624020f0f03090108010906080a 73
    0x40c0d4582e8800d4130180180b411080040c80c050000442c4180c0480d03944004c2803600e00f0364404000c2e03964411644202c00310f400855001d0381c0080f04d6214942d8140702c841541c900c0c40240040503240001d40010740745440c0c40002c0d061942c00c0b00d000340e400c0401071411001400829030302d40c600400c1d90401c01e0f024400050603803281400743c201c0394410500c61102e11f401e10b050601e03009095110501003410300b0410000c8401c42c090620116401c00e82444441d40c2712101a451441620144502e06510504110502c032512840714080e03071181c1c055800c5003230309220880980b0758008080302c03c000102151074103907000300000c0b80c010710040d006402880c1d8810002d10741c5241147c0480160b007001521510350480c03140500310000c40304104018040c1070118039110900d0803a58201418080018090a070b03000700200211800c5450443d0101e090f416041603e0f034114485e030700e0210300002d00110742c041d5680581c0f8185c03030300040106800344540d1543c0e48201c82d02e6812590b88010580845800b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 741401906 1250 741400656 741400661
    0x3080a03140c160201080a0b1306030210030b0307090905120a0f09090219050904021306110d0504080c090414011b0f17010b0f0c061306050115120207080409 69
    0x24822280c400040055640d0194440400002d10035080803504010b00705501000c900381c084510740a02c0c102803980c2d203510402c0b0040c00c12032a1329074001c0003075901e040c0d041000d030405004e486c420741d40210018170701c45090701950910400c1650603046907600b4003000c030305940300e080024080c030300700c2c1c0100702d5100c860340301c45d40400c2f0404006810a00801c2203680c21640d05070041241e000c0861615042a9550204180403403e600030400d0001d81090030b6034440d0141e41c5440c1041000449060307640343e001d07040c2c941000000c1c040b0f000d44401c0c56000781c002c80596003160288409014440e005400b000f59102c801002181c601802d80781035403441400744150311040043c00142c000d102c0c18910082c00514403001c80400300b00c501048580300d032450b294910b04580c1c8241e0140e07280c104180741d1440038014400403c4151041d20204000c16002c249004081800780070100540d03602c5aa600840d40384658082c400304071981c0c0c81c55035150842d4001c2c007403203000f041890700b41902c50490f00c09 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 741403156 1250 741401906 741401917
    0x2a0f0f0915151306030e0604050a0b0709031505060405010603060b04030602030720010b03101a0d290612030301031a090a020d110a0608010609091104030803011706060108130605060a0308 82
    0x84210f1418828071620750075105608040c9a004010503a502d06507550544d500340c05080144041241d6020440e818080c90203800516070004190314a044442400070082c201261070501c01c0d07080030300021f215070080c495031064a020351102442e0600359140d02002c0d62014118004003c4407445512003550b5400b408101c00400d031002240340c40c401000c251800c0041e850b42401c0502e402450999080400c0e0070780001281540c1c03e2504040c2801c0c100000d030500d60804980c14204190300810803800e00350144900c20031a42d1010a200502c00c540c0d03070340402d0200603c010340c1c2510704251b0300080070019034070040b95012221008110750200b4031103400c0707906c21203030107090204072407143ca400084140a000d40f8901140030358540079004050300120721640410f1650b80e0269018120440c0c2201c01468110f4030300c507a6540d4455443c00d610081d164443c0450117501c0209480c2c1d8810307002103001300e0000440820031006070300e80f80018200a8440f07544147c3d00d079070000006940c2c40142c80c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 741404406 1250 741403156 741403177
    0x101a0a0312080a050601080402010305061306080f010f1503230712150c09060e0a09060e07090803130306050a020c1203071b0c172a0f0f091515 63
    0x150501c600210242540c20701401c035280c10742c200b40c100106660300481c0d00f40d201340c09180116160310b03a900400c1300881c514540701c8026041040110740b072000098451050401900204241400f0b0344903a800c49480c1e001c3d42d9108080da9004001248001418026010001100e03031144608056050b1604100d0f034001e61101c80b0350036616060100800e008075070700989103400d0155199500c4000d0400700740740150800d2002c0e5200012142e02c520340d400001d02140031040000689a400303415103d41308490b150006140c181020800e00808020340d0160034015071015402d070f065580c1c0d0400b4160040c84004001d500740090040e001080000b10103010541824039905e003465080240200d800700d00c10340006410348508000541018166812500c0b060380300c410701408445543e08000901c0d10442c000c442c00780e080c00040b21000c401760003c03402221200d0754a40f580041c05044014502d82d95480543c004c0001c04641d10410b01e0031480d50010003079141e04100c054151700b260409145034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 741405656 1250 741404406 741404423
    0x2090a0e030d0f1b0302120103020909010e010203040f0b0c0403112e0c060501080106180203090f15100e0702060a0905070b0706020c010c05030c0712170c0703031409101a0a03 77
    0x203000fa652800841603145800c0d10b4158030302049107c150400d84c5061100900448215001420480b070a41c024110040d800717000755683d05150605244881c50310a041e110211918046070000065070125011654810b0400d660100000204880e482c0c04541c5000760711710300f1342006a80c00101e0104c8200e03071407540300d41043e00c44501b803034000c450303050b0844051a0314000c1c0a01490f0b0380640d860100301c88004000d40e80750740d03450860341020840d0000802e144951102c2261400c0d081e11150311809449941d00d00c1d4950f1024518a108410381d600d40c05a08481c0119070100c1690b08a451828060012504911741c0c6900300307d41a80012001ea9201e5404118240d40c0701081c040c400b24000f544c601541541403401c80f000842c402c1d440d00403c1010005801d101d41401491b01b0901c0f003c10080380e003494038100d81200c040e64024902100045d140c001e40e45107400340050200c0c0a024804014506544090511f00050401984c0f54200d80150110344006507141c02034039001c0d500c00c1204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 741406906 1250 741405656 741405671
    0x1113020d061415090409020301020307080106020114060d030c03020a080d09030e04150513090c03030e040b3319110f0309060304020906040b0312041d010302090a0e030d0f 75
    0xc801c8070001c2d001002100d0502414801c0d42d0390f600c4880001c03088075021a41c0d5000901c001400404420354029015400801001071366a000b82140d4102c0d5a603400074844558036561201d03503400d04403003803984520b22001c010b0209104246050b0b1041c4280125440706225440d00303000f41d0806c0c82d070304004c9502c0e04c2c0c0c154101588048681403086042d036040c07100060003103104001400a0003280e01490548138154625185034000003403154010100c290768035200e080080040318200c4409010394205000c04c1e096040c50a150b12091010305034441e45003410000703030405406010300007480040d00380417144014000810004001c0c0c03498a071130904a00c0b001c6c041f81031101001003402c00790000e01c44502035031600380850b0340c81541200c001c1c0581c0e445200040040203207000301c98052040340710f4442040503130340084c803d131381c0da000038548821582c0d0740c480415882404002e402140c2c0303c0205002c10450781107003045400b010b00380d0f414418000240803c0700d0b00c40d00c0780040d82d52640c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 741408156 1250 741406906 741406927
    0x4021606240f06080415020f030f0c0702010f03020a0203040906120614101a12070e0f030307050307080d0b27130201210f021602101704030c111302 65
    0x582507405080590700d6a0202d24144411001c2d18541c80f51000703102d503d1000908018000b410042c04200340041103407903404414220480e6041210707032982c0080480e01060032401100188c0e480c00b58140c0d0f40b001d400188500c12401b80d0090050705003984400e01c004519034040d809104007400d012241803040c85450700b010019140a400d9484446065106000142070180101c8058a46010300201d2000c0300e420700d504984a1428000c80c188103500c01e000c4019071185c008d441030081103400c604546145403c054580c821544020718503481001380b68000782d0440d000c1c00c41c1701240035001602440f1000440c011407242012400c0c1c0041440c1814214988414510b030810b4102c43e0308140f02c07045500103800000300d280d40400c182810340c4814000801600680d800c2c4808010564803030401c462811848412084200d1082c00200ca103022694030420b15690200b000050030990b64070342c0c0c0c40556031040240d90a40d0303400d5844849180365100c48022010321f000d5000016501d00034801c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 741409406 1250 741408156 741408191
    0x9050114100e0c1303060501170708030c0309090c0c0f24100504020c07080106090209240318121902060f2403070816051e1e04021606 59
    0x8046141512403540144030760b0103904112a484a0883c4046549001d00b4420754810740803a407000344428142800402c14150840c0188110420182100d5889403201e030115201d0003801e000e49800d60042c0f04000d05445c0c00d48140c1e410800c4601c1040c036002c2c94400c414201714403440f01c208c80358440f0f0a040e044040480120718015090481d4020300c1c1061041240400114815240308076008104220310120512503070000b860036030000c10031300781d98940e9000a50482000b030b511541000740182807981c01c4100109201030300400042c5503554018035003814045110f01c50416120310340c018150705103004010400c1d02108803089402d00601c0c0c0700245050f4008100c540700d1400303402846003020318004002c081070304040503040e680d071032400401d14113460b990001c1000d01ca030b0380f41380c2d4110301c00140345030a0340c1d419214501e0310001030311600f5108031200341c520f81001c48032042862480402464080c1020020801340c03408540035400d5003000356610054074140ea951403403c00e900402c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 741410656 1250 741409406 741409411
    0x9010905090307060e15041b0b0f03010303260106080115020a03020c010e191701050c0f1602180f01210c23191a1213060f09050114 58
    0x51109000c140760500015450303000d00a40105265104c0b01c072002c2941042c459468004c40d051801c0c41e03185072600b0014030301110a010a2454014240c0124100e20500100e40350041d41e0074000d80f07164030750341c0c0c111054850100812605081c44036000c280b0900030000f45d0084c8140e554504080d41848515403000500300c0110066500103802540080e40204c1d03114010a42424000c1e0f02401440c00300709210290301d102c4079440c8159a000c59490442c2040441007610100200000e80d0390445581e401e00c180400303105c0e0108184034441074140c01408042c509880501003040c550f41c0c0360805000c0c2c003010f50f01454008000001445030940c40001c1000285034024105107210b15612082d280c10b0f001c0c0624281c0304007964903d1408800200703138100c41c2c2e0010303003058081c1d440d0380000c2c42904864007640306000c1a0140c12009100070800380d651001c400302c01c400640d2980350041003d0003510404035111502e07151140c021580c0c80c400c0600700c1d0f020b00c002042d441080342d01c0301d0041c1c000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 741411906 1250 741410656 741410669
    0x905070609180f18051e06060a152a0212010612080304020301060305030c0d02060f0c0a08060d05010609060303030513050a0b0408091c0b06041406010509010302070b07030b0901 78
    0x908100301010649880c0301040b4034040001802c0112683c0e0000500701c1c50810319040701d140522a400c000000a0101258658001c6980c2e8180c4030400c00d526458180c804680c800040714040c400c1280c0c841d031070030000c00b0906004491880e01c104044000c1307545d0b0074440c0350440544141c020f42c20200d00e6542c03090030f03120080100e04e081409004d13440f88510b00c090500720001c00041c003151025400200a150048200d03070b03d0f001000307170382c0780c0d68580302e08000014000c0d000401c41d682590210319020b0307a02c03050881d041848120044030000d100800659119104d0075494010132820721585000d04a07509000c01c400e801e50a01070309136080908580807042050742c20a022270008100c400a1542c4082000029259420101824054454138503809000210400c1585580009848000c2c1c491a902d401d250740d103c0401049440c25109640111001400510707103601c940c0040c8035400d0141401410310b007407030b02c41c101c402c9411600e10001c2546c411140d1441e2401c0140103004121 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 741413156 1250 741411906 741411917
    0x4030f0e0112021b030f09100306081b180115091418040206041d010303110102090a0501030c091206020a0206280506040b060a17090a020d0b0402150d09050706 70
    0x80ea0300008040d0718003014084400c65002c1080140c01e9901c03000540c103509140201d986440d02521b0200941d84100c0d2054030920906418010300b0f4000d001e13581c2280e400c5805890800d01e6900040c07419039040031441e500401c2881d041110120032000c1074060000281409110484008003410a40d91a00420031050001d0003064186d0780d0410b11202c0300c104c41d00008483c0e265440841d00310300854100e0030350070742d03005088062210b8954005040b80e01a030f640d0010b034114004014201e1041080d9a034102d407820009104030b500940210103214030a291a01a455840f240c4480503900900308562040d0001010b540b5140d04011140d0404d41542d17400300c501140040c3c03031900d0046c190089000c1620b441c00944190b5959012014501c406013009039202181071008080501180303c43c6040040c02001c41c118060000d08034200c00c1e4060038a1590340e09684954001400c01030041f44d00030221100001c0010426024015419107d100496070b800b03540341030760424207550044020400c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 741414406 1250 741413156 741413177
    0x6011209170a090b031305070608060d02120c061b1b03030d1a040c020f1b030a1e0c120c1a03011e15020c0a0e010f0b130806010e04030f 60
    0x959000710720104401c40c0d107005a0355284a507040d40c0080541c0d00000c040c90303010082203810007142040018140c8144203807000140c91351803d40d004001501d007160081280b401080060a04404850070403030301800321039500d0034041c00a00b0b070b1362080e14459403046a905da0903142c10002c016040540340318080003481050084042a40d80c0155944034400c0e0342c5038055003105030f0351904a514440030240050000d4050100042e513180e0807030500c2c2d0618451440d50506241b800c820418401600401034152520581c0b1085046080080d45044401a80d6a01400900c01a40c03540042810704105c41c800503807402d0118001d980c83d03100c01c0b014140d5031400c03420120001c2c01c5a040d5940500342010030240300d500004010f02c0d0b50050b503d40e0003d03581d118051074002801003501001216800c41980e214100008101d50038812580c0100072054244048516030010b814034200d10b400360007005981d644494030300300c8207920200e0404041400e0009140d400384003070300c504416050003880d05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 741415656 1250 741414406 741414413
    0xb0103062d090219120b0604090606020c0405090d0c051501030507080f0c09040201030e0a0b101e0b09040c050c07120209060102011406060f0408070906060e0a0312051602090f06011209 81
    0x1804c00e400e801000074000d0510800300c07443c0c0c000c0004c000060952502c581e21614103500400180c01540050300c91040c0540700c52500c3c2c0201c6100b102a03101900e000e9180041c1601c0d03a50300007004956502503a0816035113144540040d034001c6010310003d0141c1440c0c918114100390417100f408071070350007079a5a810b840e00c1b140d0a00e40c005a081ca00040c0e00e54a000386d040c1000813640009002ca061041400101c01120321035600f9203d1819646050504200160350714042c58481e0781c510070414054002580303010341c004401922a030a046181131501c807030041c14145a504000070241d2100c502400b0340c01c0c50481c003030f4810740a0000700411a0481c80c414082100180708a1103410000307240d0100100b4001614014280001211101c0e502c5030743c16405040c5a004e00310001d010381c0c0c03900c0c00b1440d10517484000c49404c0b0314a000060240c203821902030f0700c00d900103003a001041496100507120407031000c2c41078060111040701030a190000502d04180260316803100c86c00c0400340c1011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 741416906 1250 741415656 741415687
    0x18100801120305040905130533071b05010c03050109020c0a0f080c01141b13060f09030215070204110c1207020d060603050313060f09090b0103062d0902 67
    0x566209004110030741c59985000c07034041c403960304007401c007506000512030038402d525001c1035214480c60645d60340652003462640c61048046a03022000340d101808110801d011540d04c2e0400c460340f60000079001030341042881104524400c8986a42da0032140103519810701c5a54050078142c01c2c10762070460101400c66503266030201c060030703804220101504110160040701c20140002c4001d000c80f249904000140038021100c98070040c900c102031031650780d045402c860741f201400c7e0711103048a0400341c0859a4480d4050a1805d2142c4401c01001680c1c600d04142d007140c00c0300503026a1264a44144025205a000c422507400d23010700900d022810003050301e041040c000d4480544400e6280002106129112800340645280081c0401807101c0800104080c820f5020294140395843c3c100300d540221042c45000015086002408240e0040d00500f481c12014900450a151546110b00e80745041c0c8a400303110000503030707031094032103840058076004080d030010850030029030001a010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 741418156 1250 741416906 741416909
    0x40e0c0703050703032d0b011e09030b130c0b0a0f0e010203030106050a050f030925080a02062b0c0201060b030405070501050304050a05070b180d0f06050703020c0f0318100801 77
    0x516441306c0380d404d42c030030381407981a102d03810b4a41c1c0010b0200d0303c00c0e00e540082c403086445500041030320b03440a2121541c9040400c04200c2d995480840c0c07031654443c1c8072074500241c1650201905500c000002c240041c080c0805130095515050703840d103c450016200b4a40c03c9000014000d803040c1811103aa008402d4070704650307103420002e5a40f1490704080703a403071141008660f40d1100c080b0500404140006807044480075418040c000041c5c91480c046440b2414460900940c6c03201030a1001130034140090099440e5203002c0885c5d201c14034250000080c5818940040550f40d40c1040f03440030b030b090040c10010803000031160f246091680360300e80c40d40e00328010740b418440c002004c1800c0041c1000f10401554104060b0f0b54410348441580d28603600c119080d440e88402101c0682c2c44c1e180c441c420200181d402080c40700f507030a05507500400f428005108001740f641c00d000c00f2198040030310030260070b00d001001469680500c0e4891100c0c617488110b80354000c0f4900541740302c0c61504000c4050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 741419406 1250 741418156 741418163
    0x70f1401120e03070c0807030302010c050309031e09060a0804020f0103020c071203112523011101200309070f151b0204090605060301060b0f0906070f0209040503040e0c07030507 78
    0x141c108500700d030b020300d503100c0c0c12001481c014205500003282640403c103142603d10980c028804d1929040c0110f840b0b000649040074680c100b0050803910403c21851100c4450410f18031038103003100000003402581280c0c01c05008220318408200c04c500e04a1952140d14800f400c085040c2044c4403062036807811680107088801038038940410034980540c4106040d10303003c40c01c070303061000c410006201c910022440b1418180424a000c61084006a103021103407a014482e141e001c2040030045850200403581c403081c55503151a144a20340107040380040c0340761030564840c0d89042c589006413a0042c00e5019814800c0c0c0801d06101544008003c642075031101e150110340100020700d401d1103400550b0000b9403192404003483c04100c226040540310308022002000195540c450a102c2d03031188008000210307a0402c000e40d40c5141c510082e00b4203038007901c0c1d0040200ca1a80c007090410109031420346156102140c20000f080401482d154492054158582070500a03507025181c0d000d002d0004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 741420656 1250 741419406 741419411
    0x3081b0f03070b040212060106200307170d0e1605120f0d080c0f0d09060f0b01120f060504111207020c01020304060309110904080d1a09060d0203031902070f140112 72
    0xf40c203640e41e940001d070b8681b030040700351440d43d41e503000040d00d00d040c2c00790354201322114440f800e0004007001c026a8504e58000000000080b0f1880c0c0000141e48400c502410203661a80b0b070135001c1d0820044102d0342c095840200704114201020071490140e100e9410810b80d0000d01801504800801c2601281c50181031245507503c5004400c20980580b103000718800c1c401017200308c0c162007a0b4005510840c024141002940c0587c001d00083d0b0303051205960200d1034405090444412652100d00104c0a11900248c426150000141034030002c4441110458001c22038504a2031241d08031504955503000405406442900103074581c040c0d41700310020715980d407200200b0710180030b102c00ca03c0000100340c07850f540380ca45410f021a030404c251110105140c80e404040d520000c0000c040c800b03100410703c00b0141c0e112000c103e00c034070801d403080b81c25000a20540d0742000c4860f1710042624007980140c13003440d00b401942510700c0752551003150400304040c48000c4690300010002c3c034512004501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 741421906 1250 741420656 741420661
    0x21c05090a1407321207030807060606031d071806030b0f40030c050d0e040b060f0d09030201110408010e060106090f0b07050a02040603081b0f03070b 66
    0x2480c01c10900200280c80e0400030001c0d410101004a074510686003000001c0052210011024020080d14900305905610b140c1c420401490304210000c6031000ba0307000c840c003454030f079602ca40e0160040b280846195440d200c05008050b0035001cac0c1d03150314843c000b4029001900384030300d640d00e10891045100c14441400e42d4179a410b9150850f6001e140c00c828086901c2c00d06451440c80e1440072075284000c200c40640507042000c6c00e001080d0001043d038070000040342440400c0504204207007084080c0425441e151000032028461903940300000d4071900c80f8081c401080c00f00340d1788681c2e900707407103101c080003030125004e052400c2c0c8688a1401100040300700c81881c041c0c2c014070020b41d03440780d0640301240014001c2d070f05400849020402c4000d550f501d0b40e84000a50f800d1510f40110440c85030390101c2072250407111000b4120072801401240e20014503500032600f140d880d50800d5540c1c4900285106007a114654500d00d1401818000c102c03c0352000c01d000d45900a1030801090907611101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 741423156 1250 741421906 741421921
    0x9051c0206161a1e0702060106091a19020604050c01050f0403060b0d05030d0e010f0c05070209100906090b01030c0206071b030e030f07050306010b030c040b031807060e010210021c05 80
    0x107250031120f00f00c0000c0d0103604002031880d200c20f4214400e50f1801822100058139203101190182c101d401588602400a041c080803100c10034000e031000e42c0096042c0012000001ca15800c1c03010042d154015103e40d0030f003401d0046c01c1105508015050010820946000c0b103110411101100e41101c8001070342c0040b1000600c0000c1480800340c541d21010071401c0020405034480210540c489000304540346030150007000792042106800e0111301300b406840007505207107612562202c11184801012601c03086080c0494005030001c40f041641d502c842e6090356094820807040310441e00040c1504c3c608030078014421078620540108410580c00d800b820980542815041010002d00b40e540c43d42c07419200039a5060785210340780c800d2241c50300001d00e40000e074017100c1c0a00c00440c0c40d18909420506210616800a001c00c241284100072150800d8000d0005502505980d52102d907082d5040000a10b420341c1004a40c180520400003081440003c07000c40c480d841c41004040fa2030b5a5020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 741424406 1250 741423156 741423173
    0x12110a1101140c030604060e101202010504090504050303061302091f0c0204060308070c0b07031209020a1205100b0a062001020417150c0711040b0f060a09051c020616 73
    0x1d600d002c21100d540305100c44003c81c400914442e03181520108003456881c040c200501c075050741c0f001c4c0211185082404580c08607070900702404d0060408500e816a2200b0802c1243c1003142c0036101074001000340503003490704820303404125900a00660920b0b140000003405242c0000100d080503901900c1c0d010f0050241e00481c000e80d4000b0020000c5903901d00f010a0745078002981118140411a404070760f290134481030369502070f0190354010284803000000f0004081520301030703074407820300f00340000c02159942c80c290b030310b42c480c1c0302803c02e21f00c1c0d01c45a07100b42e42c1d0040d5240c0c4107211301c2c0740c01d00429130301000c240c0100348021001c081c0241d282100500a10450b040440125105045c40302c400c48001340d600810082c5804a00c1c03190f5440d54000380500803e6030040a1a40c5485008501c2c1b42c1600140d981c00001444544848114000121035500c208519004100482010012842c1c107901100049001020304203104039298001000b5102d2040c01104041f0000c0e0344109111819 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 741425656 1250 741424406 741424421
    0x20406080d020a02030706230304051011090306061005090103110f070f0b130201080f06131a191214010b0d030903060c0903080a031113140112110a1101 67
    0x140d912100400c40003d450308900041640280300b48a40050100e202c2c0803c010440207a801e07140710031001403038950703250348003400c2580c1e00c0c8983c0303940c843d200031507105400d00526a8560140c0e100c0c400230516081180c000c2140784209041d10102c26201e40100842c0da4141007481c000811045103002002240103920140d45000c001184a5082005c0005d1f401e245074016011401c8503507605494146410031400000c3c0010710b01c5c000b2480c02048000b8103600404002c02d0992002d550300d00050458640e202e000c41c82d0680802400083e040c60260007001c021194543d0540302e0401070f6241d0182c0c200c03070b401000480c0308004031800070000c2d40942910070300107080c01c035100601d09004004155a00094503094940070040e04058003908203042125880303c0014188910340301c5c190003d0220681d01c0ea14054104107420303010f110344200c2c2e03018010880191004051071000144a6408648400304e6a45002010100030105405846220392145400203403803c817001d80318050f1240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 741426906 1250 741425656 741425669
    0x908070506070504050909060108070323010f021317060c090d14060403030509190b130807060509151015092303010e150a0b01031d2404030e0904020406 67
    0x410040c054441c0e8400f004004a4808a0f0301540e25169418007644944e400e1246401070f602455040000840e010f07650540c00003100924030031014070104c1c803829580b003084034203002c1e40d0000d4115200c2503109213201c0070b4001ca00400c0d07440e0710008102075032000e004e002c191490b01d010842811503690703603440070141c551009030017541e5280e040d41540d80f82c905480c2100401d06000c00151045000506c0c08000b00710304400458083d001d0b00c828020358005001540d1740f110784290308011410200040c10340d07602c50240040e541c40c0c050300d803906001d410048005010030710342c2404008251603600c0c40c01d0700c0f5011182080c00c1110308040c3c43c41181c0b98094050455507620740b0141e08103c84d0320030203850050380240804510110895182d00950369049400c0069401198458060303038406040100103060008030343c00b201c5a901c007003500b90305901e0001c2d486035224142c00c400b0001c81e0300a980341340703081c803005050076540a444040070f0008140034443c2800060155074490f004407005042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 741428156 1250 741426906 741426913
    0x60902030708220c0b0708091305060414160f03180f060608010b011e05070b0a050402030f0d17090a02040207050304140406180e010b041b080108120901121401120b16050301060309080705 82
    0x10480e240c00036241c211005880f0303d00d0324507000b6219507400350041c4680ed000c0c44940400350504410b5a07030b407119a54080c01c1541d2484074284001c40071f4491512039004845120003042d583c941038082c3c400c181c00c519100d90401c0c00162492b60840300101c030818047c03100c00407030840d61504541500130b00c00c1c09001d107480801400034040c0740b680701c2c42c080c0340260280c4d003203441074540c3c441d920700c080d8045400280080c080b01c0035003804213034110b40200040e4180c803412111900040c0503600090001d4a80d6000002c040104108440307022000200540301404524508594010544401194400c0046e1242000e89402400f0340c095a00e40350001e20070040318149c480602c80314460501c015022030300e90400403d01007800540d00c0601c00101d0405443c014058004448062406c10f260300507a403190071204955054448050181c18907101d44100c001c032604001c0e00100703002d02100000c007941e04089094a5121048071305461030b80c100400c10000071314103600e140c464050050070700d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 741429406 1250 741428156 741428179
    0x50c030102130815070503160903170c15010b0d050613062309090d0c150903030b0418030207031707060e0303182a04060902030708220c0b070809 64
    0xd41d840c110b4041c1c0f030035101101d10081c1000081410300100352408401b088003400040d540c440c855800503503404151400144096981e520200c413081034940050015202060312084054100060b81c040301c10030741040c500b54501400d070b5089200d00e01403140b0349500c40c0001030242c0c4851a8441400c0301c050b03000c002503aa030340f10304401005040038030000c0c01c0407100040c10030b2914002c2c690184110030084d0203011100b4074103131050700065a0840390748400d0129000c103060702d886040c1078a0700039280480e4480000301041f00700c6010007030300c07a2100c400d032141401103940002d4840c00d5903440440d403940351b034001c0030585c1c140c042c1c0c02d40181018100b080080d18104040043d5008104078055003008481e80c400c09512200e4800304881c41101c407000c4000714109600f03181541580140001031340c9500d0700050000e0341d00071100900820250380c00d000c44220340c0202065080b00b0440030340c807180b440e542c40c80c050800e14032505520b01f001041c40014403444404580c0c0140004003040e2108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 741430656 1250 741429406 741429427
    0x24150c0618010f060612090201020c06030405030705010c0507050a0b07030e12040503070504060b0703050a140711030d030e0c041a0301020a0914030601060509121606090305010e19030507050c030102 87
    0x30400c10001c05641d5007445403030240e031903c0d13008060545641d612060140700070240884014031940b0400c1c0d0440c4034030b880ba1582d40e1a9800207500460055018540d10401c40c01d01a081d121141e0301141001001c0001c28080750f8003060307094100c0c2c3d0002d420b2850b5243d0fa4002c8003d480e406200000074080c020580c160328081400900031905c4c01c4c0c0944141c9580d5004000440d40548a4400f01c401e0800013800000d02c41c40041c0300886944c04d00c030440050420b02842c5a070444c40c003c032540c810420303140a4a1804012040f21001d1915061000c0c0e030b44400082e445070505640346000d56240d41c00001a014440040702503444017030300854a810001400610560312403103150076150500004500e41d04011030914140c45490b155035152842003070501c418003101c58010100e500481d640082d40250846810300201080e68619110303d0035824060700311030607074040e12480c2c1c0c000c190f5401a0000f00c42c5140100f1f4160038103588403e11814980e00300381c1c070784440ca64154800074680005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 741431906 1250 741430656 741430681
    0x307060f02090102120f1204060c1b12111507030b0109290d0b031c02100504021f14190e041e051302030601080105070824150c06 57
    0x115014840600015a29454500480c49031440c01d90041c0c100c0e100f00300c0c000b8005001060200e10800c81d542ca030a201024600d807089080d68100d4a04c1e80b03030004001c03001d92107547e0750000000c00c64204103404041d42d80e10301946001040c070040c4241091035510259090140c10641015941082c28600d02100018000c1844030845404036101c03c1d030120303512041d15006070303020b01210041d41000c0c0e0900101da20030340210420007030075074446030801c589490034098911480d0460b042c03002c0700401310b400230303050140b00c12030103000034500310410001d070340d6440c030420902640101d80b070031100260108a6030030340e200000c5038041e500081d13609110001c1007811440390b44241d50f81c1411040c5c0f80100030580c0d004a24400041c55980c0040816440a50000b0f0308511100129a010361040e40800c0c11f002c02640505096507640040004064014407440d03888614102c1121281108820320090015040e200a0080754601555000001010200c0310240a140304844162801d1014881b0303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 741433156 1250 741431906 741431917
    0x3060a26060f040b0106020706090e1503010c0905090a090f0b06010203070203251a1206120111122802210f061002011a0613090c050c060106020d0503040b040204110c03 74
    0x2404e00340100001215440032902506030703003007a551200c9c0c0e140303000e100e5005440003508510303811900781d03040b005a46e824800c0203c105100c1e2101d0038014540000c1001046e4010724a907010360824000c003000a803048072040407540e100c0314445440d112b04004070302c0c601608034000e401d485501041c81940b00c600f440780038914640d041d60480c40c0d4a80310102c01124160809406180381448031078058000000590b902c05405407036aa090100040d0090035070b1520254030480310400124030100340012300410341e2082c43c210300c0200041403110300b001e016104600c0e03507200b00e82c0410103000151901001a0710741c81c82c90006811410f008910004036042601c546100e00100031004c040c0e240180079803050300c60108141f02c011002c180034032070f440c0e10642c50700b03120300040030340030800301703410b00c42c0c4c00d80c0410994800e91181a80208146003d40c1a04210f0940d0300c6450b1702010f40c4c0c1e10004480d44103a015240c0c3c8020744840c80071130302403c4d21251060800c0d50201e008110030000202030032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 741434406 1250 741433156 741433163
    0x1710030b0f0a0509190f05120a09080708030c07180f020a031a010e03070510030905030a110706140a0c1a0103031d0111060a0e0f06040c0e01050603060a26060f04 71
    0xc83e40d1903103c455541d50304099000c50903006070740300080c04a411546210042400348080e5500c003640c44128034490392004c04140007150010b41d003404020300070009075010301690002541307800401c0d0401c07540d4103000c4c441c5481e22114143c04510f0403075190444c640c040603000080d034032000b00e1880500038240d0415070317000401a616600e07400b50b00c994803a0500400240141c8500c41c104014800301c5c0c9106611082895151800072000860401c024110404030399141540510842102c5041120390340c400f4041041092103039011045200466414264a05001d80c282c062841e0003000c090020b05152007c0950070000018541c001442001500080f0082c005401c030400065403105810708440007254403540004421140d240d104640042c0d00300704440c840f40e4a60400d030301e021021074080b104100684810414406d01c141a076000d171808944850031842c3c00c50106010144504c507440c82840b04503410492007889029034a400d0762448141c030180e19041c0303650945038100ba601107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 741435656 1250 741434406 741434411
    0x6060408070806041e110f030a200f0d0302030d091109070e04061d040f1115091503060d02101107061808150a020310240e0306071710030b0f0a 63
    0x140c0540e035584d805d20b14a980c4001c81a04c220000018003011360040c07280b444e0036209802074140424030318076036004a580d000074030f0400c02c410441032140c103e460400c0e0074000d00401c403100e0000b80d00030050394401c0402e00c0002568204a0611b1030b0107051140403a90000403040600090340c0d030044c03841c0b5180d0400c1c0c40074004903554003001d04a030b445074500300048072440c8012400040c02c68000002d024081d02143c0f402d09104d8000034080304000f1030800c04414001444081c03410079011408400302c02100050540c07802d00e0118511064400b4020b00c111819603401d81024022450740c804d000030001142c2d400783e150341e0041c0214030b144035031900500080b070000502400c0007a2006032204800740c1460103445102c00c18001c0d40000d41210300b034145410010809041280f4029401c1250645901c614003061001503c1060417001060081e081407041180345030300502c0c3c075401c2507070100c60b5241607a5602c4c4800a17400c4a9000241f030204400f0900564410703000200c1c0c090707907014404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 741436906 1250 741435656 741435683
    0x20a0f0201050c0c0d1206051012050c040e0c0a020a060e030408070b030103080412080903030a080f1b090d0809091315091e02061209060702010e03040b030f0606040807080604 77
    0x2400c1c0c0a100e404c0d4105030f101180c0c5240baa8491401201c50111280001c2861030726840010b03880a148010100020039003018048158064061141c1000108220906c2c041c14502041e00c01c040081410310b104100240c2003404900c02c02c1400541a001a0300704034400d408004079032a981b003881408071500c02c0c45d2002c1040303509002141d0403680e0001c0e5140c940b5252841c19258408841070669142105005075080d980b003c3c0000c0a0014466980700010310b01201c07050441c1c8030240c40c0c100a0300384080140803c1403034070b0440f580a48101c03503140d4025418034001c0e0441c400c0c0e4440c181c01c18419000c0c49011401c034948602c00612809401100c2c440c40c074004022166412805840001c40f40c01c140c2d00100c079000d49614450002e0712441c504607501c0300c1c000c2c1e084400e6070f075070005910280070030106030390a10803989102c80e084040c600e0103107002c0c1480e06501000e0241c49819482c0d102280142d640e00d0200c4004051000695410542d940f101030f890300030031181660340000e0142e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 741438156 1250 741436906 741436921
    0x60907050a0b0d050709030b0109140a14010302011d1503010e16050315010e03011811060c0303060609040b09090102040801050f2205250503010f0203090a120909020a0f020105 77
    0xd280c01a10420002d250a210f0742003c0203000d0500a0705a40500403090004000324040c3e0307a0b010302a00054402103101310300401ea54901c0c40005182c100020301d001b03456100c44180018017411250240b81200940c1c100031400c0310055840c122090f40001804a04c141c2800c4100140d4100c0d45061b5041c0d000d551416100c4120004c44844400060700800001d041c2010304031715608d040e501890080144d070340324404a4210340340321318520200000300001104200d80c50a102c0a1180c0943d020750a025100014a943e404080c00d014455a408241a40e094846074012440700c01c0c0105034064900704200c8a5000b54014011030242c0c0d400c1c00b001480e840700407459107002d1105003545494215810401d101a1490720404803020b000c1d10300240640343c10310303248060410803e0346201c02e047c901400c02d421500002c2d00c0c2c80c0542c2c01402000b07070303480010030f075200625040440010520710760750040300c0540a50b0008003001c1d101162000038030381c0c005128649440c480c2c00811054503400c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 741439406 1250 741438156 741438169
    0xc171810090e010b0c03192001060605070b09030906160605060f0927070603020903010f090f08030702121c1505090a110712020c010219050d050f0909010806090705 72
    0x324180c0c00d02c4140100120105100141050038044c001d8905158801441850090300e00c0c50020000b103501c04d0f03e841c1004a070030348000303004d1400002c00c240c0e4075100c8041c00900800c50040c10200110000401811003401110600d0000401c030641e611000c1c141c9802c1e0120105080c4d41251520000a195003484c16101ca80d13504010100300340c6035280004248240480440d0740c030300c001c200028801041302080b45034007a121a440240c0c070750002006250846107a070706009a6281410012004510481e04810419810902c040c0d0740c0e5660007016880e080c80414070341403e00b00000c503410a1003c84104140ca220750603014015000001b80e01c21403030000b03004040d801011039000c680584032540c0958000c070340b400f0030300381041821748400e410007a400701d26a001d600403c90b80c84456a06021204644c00c0e211883d4807203050680310309030f481100c26103640500000042002c0c90004a40035110800f0005014500a6841301129625081c003034600d22414418005d000c40c2c240f80c0003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 741440656 1250 741439406 741439409
    0x50417070308130809041d0111031b07020102031c050f01080307020f010e180a02031b070c0909020f210d0c030219020a031217060609100c17181009 65
    0x1030390b65040945940c0c0c2450050b10002008503060b00c0200410a11600c642c011804840340c6400f94552601c40421407a00f51105e96442da4a06501002006603504000d000b6903c848200c046407600c079031480c40140c0c034522443e84590254020040200c1e0058015040188200504e448541e40d50340d03280011a980e001c2c4480084d8001c0307a4030400300055100c0c01c078003285200000c08085640300d16210800b60803209540104030b1a800200308150002c03203991038401094140c52413444c12030542c41d440400d070803900662080d55100d5000506543c1c80d0150003c180000030022000a00113910b01040d071210f41c0c0c3d02d0034441c040c0403880600b050251134806480c41e01038002d13280040c1c1d400d4142861006040702241d000918400100218226091605801d00342c1d840c3d235044404c000c081d10306502070007410b0a200d41000c00160300543c540c0300c4a02c1c640003403421700e40c2c3c0014151500140780c502c2c4501c40c540880300451481c5102240403d031a141e0365040e500b082040ca14800120b50f071107400d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 741441906 1250 741440656 741440663
    0x20307020c010309080f0424080c03042012031905030c04050d150e071d010303091502071a090a17030910020c0303040303030e0d020d020615010306030f0605041707 72
    0x14040712841d402600321051080c8902ca4051805a1022a800c883c0d0080d4010410020103c02401e8480c000c101c5c881f10000c04a0802e80c1c0d103494040c01c00b02c0644401080109a8900d1300041d8914100302a840d48258400800f0115107a60317860809503030385c002400d90345603103e440c1d6a65002d5401a0304580c01000c0301c490083c541814142805660132442e01e0468441003413085a03402c1c03030141d00c200e0144110306009091401c0c6040031400e550207000c03c18000d42900c0e40c004000194105510b10229880e0602c248c4284034a0030041e0700b80605588014801c0c4941c0d8048000c074180c0000400a8480c12030350003080342e8590305c01c0341507010b6403110152540e00030080740c08185002c04241c00e0300650340c81141d1070f014070b18000ca4155080f0380e1048000c02c2d110030300030f0700b0040144540c01103500140300900803040300540003591008090b000c0600850110305104c0c0320303403283c1c001d1805560400551020b142441c60320400500c0b007150182c0d5850419808152401c0ca040210764100d42c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 741443156 1250 741441906 741441913
    0xb07061b02100b130f090c06020d05030402091f080601170a0f030809100e010906060510020d140702040504080301060f022b0c05010e01051603151a040b03010f0303030f02030702 78
    0xc0340700c8004290070107580f44c0c00080e440c4070342c628414a0041407008500504d0200700841146040001701c4042e800840540d081044807945041e4004192030780b15404a4041c0740c9078440d183c40341d0301410000b24081c0408241030b004502c0803000503c1c1412141c000b0360352402207500710322540d22081041c9000702111606120070700030030311600c040341c0c214080b202a29020a801c4680b07800301d0b020310b040841c0c9651140d10920070b1000900c0391000815040c2c600c4a089084400e00039210b80a01c0d440e40140001000c4904004200b0030a0383c0040d07038060020072480c14030b41070404940d00240f003000c0000b6409810300e002244085503641800350f150a101603200880c41002c0038090a01c402141004050b4082c01c000c900d09000f40107460b40302c2800001c0d01d05091102d141e8104d038121501d03041c18201503154040c00c1c4440500e00850b06890b1140703044020018410302103124980c00510382e02c02c04000451a4440b1080003000c176803107070720100890711800307008206901040fa0004056007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 741444406 1250 741443156 741443173
    0xf33010e10140c010608031303060b0d11040903050c030d0209090c04030302031b100f05070e0a2601090b04120908060c09132909010e0411150c070b07061b02 69
    0x22440c1c05003041810f84000880c600d91918111482d42e0403842480200d42003000e0100300380003151162942140c0203236102c9460030090f4880c1c011141c2625100c50162b941d407904541030510500a1703840b40300b01d0405880d0b864001c0f04024001e5001507024600c41c1c070710b80c4041100c041e5a5001c482c1285e5064002c1c5081c0586d040440301c501d4860180f516250180194401e000c80442c850160422481c100016050a2042004201e4881102c00341e003d696042414004007003900c05000740780d00c070300309040c1d41c29051240c0c1501505840c08001c14406200003840704000312082052481c40040da01c29441c147d4612000d40c0d10507080c1c030380c1c111250341040460000d08050100e000c0d00228010085101038041e1800102c000d81c1d115101c1c4c0080a80745c503000c0310300d460014180101140d00c00c00704142801e442d5031040a030070f140c88612a041400c9220074080a03034041d245c2411028040d140820741e1800507684907400402c080303601d1407034048901d403800b0158200c1a0a0780880d401400280c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 741445656 1250 741444406 741444437
    0x510050f0d0f020a09061d010506040b0a090e04050309011d010f08060612010b0409150f090c140a230703021e1002030a0c020705010503010803030f33010e10 69
    0x800303012106a80500d604800240940c40d030706444d400a00705240300041c600d04e401d0700b140406888044103030350b0401c1007004201a0391603005460507242800d41580e034449520301d083c2c81e0070a8980c0a8011010010200028040040050148800c00b0380350129400080111211100d0300500c207035011a0201200e1050148500c2101e6400030000d080b8900d01042050448680741d402d03400032200c0725001409000e042182c0c00381144a011780c2405152803410802c1100000040303028002140d035072001284072003481003441c9071408028512040d03450b2140c0e540141041501c200106800b515401d50754410f030380043c1200d070342e40c1c1c056014120060010300c90f1003111509152140321407080200681201c00315100442c02808000c10004400c1041500681000b006d0390015050203c2440108402e480100c00c483d40302100c0201848a40c0d118420840c20604085020108100348100e0107500308119400305003900c0c01743ca518076842c140c0000c0101d01840500300b040051b00280000b2441d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 741446906 1250 741445656 741445669
    0xc0303230d090c05090f09010b010207230a0f0b03060103050112050a1205210f0711030f03060102031620040203010b0f0d0b091e31030311030c0c010510050f 69
    0xc50f44216034001080382d0703c20000b5901c0c0b00c26250008600110130178800c03803000910a420021500380007810a07907182000e100d4020b485d540c05039030300500104047c452941c03546131480240c1540c48512041c40c0e15152101807907001211218080313171801c0e0001c160002007590501005600900070421448196203010f040c200c1d00e0007a1060050070301c10507032448400403604417414100b6054a02918050154888001b005030599003403118020002c08803040200c12544000911102940d490700c840c0c004038650300c200d00c80441c42c0c545d0100550204000010b08806d0b452020a0b00e0341905208010001248030078400c032490880100401c841c42407000b000751110000103200024806071040c04240f054004607005c88041c002c44118841d4a90104049900214000403410200040c0303a003043c0c800a4001c0e000d602524540c8010040611980000100c85101c000240e03e0341070261b640c80075031300900400c500d15403c0000042e242c10f0540030240460781c00800c03000070701006000b803051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 741448156 1250 741446906 741446921
    0x100213050415090f090614060603130f1a2d01120c030203070312021504030f05030612070f3809060d05070e010305090a022d030a0c0303230d 62
    0x80611868000148000e8612615496013207140000c11440e40318600503040b941103420301200c00c03980c54248001511000c1c2030b254886c200c031510250012007802c0400e41c0c0c00902c0c0e07006120500c0d404078030522000c02d2040c5806012004640400707001060301c0c983c03007034a01c0c09810800c5801c5000410010440c84100d85280c0e00a0303000c41881a20703900481d0809000350001e4801c40d80700040028095810082c4052966455021100508051350001c200341d51b104941c1c010003c002c070214819030f07200300e040c800d000700d0790007183c952981d070740c510790308281441c070441440050747c01040010b07807507010070205462409032030b900c0340f0a500c039401e200725045000c21581081050004c41c0c1040c41d98400d0b5401801140c6513080c03607000340c40c001015201c4c010803410f240d4028000030780060315a62000050440414810700c036185409140340006910180c103d64184a07442d081001d0016100c40141924080c0e50b907003003c05666462019170040040032030369422001c1104e844200c0840c0d02250 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 741449406 1250 741448156 741448181
    0x190503071412061005030c031b0c15090c10020c09070c1403031f12020108070e030106240f080a0b010e09281a13060e181002130504 58
    0x1051001000c1c06840c98004504a50781c0038280001d00c092450603802c101c0b14600107107401480c5180000189111f8003024020258a61911184040090325107050340c0d020341002080710700030707000c19a0741a030442c410b0f035001215016510024155042003040030107520000e03001055006429424800b555100074a031104021030004408009042403180c0a50007004000441e01da0410305100348040c1002c05803800c511103c12010000c640d100a1000e02c5d081d024280f10300140da031220280c1e101014040c076194594680f841c04150901400d0001311a40ea0813070b80714074007403404c02c416030382040d40440e00000714220a00246550303480780c11900c0c100d00181b4146019410003004034010f0003090fa820052b880306401080d100d100b0410344030103241c880c2e00c018031220413001c1840d080100c1c0d8500d464015581074010036404116074000000a21181403c0e800303070300c1c0c00300e1078607103030a2034010002950041903001408101c0c1d600a0302c2d411982000701c01d6040d840c00c401c1000820f105600e04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 741450656 1250 741449406 741449417
    0x1a0f1806060d0c050a020c01020106060e010302070c0905070c03081012080d11031003140109080d0b030a0506090c030f0606060901050336071a04050d031101090302012019050307 78
    0x40c0c400d0b20981c0641c3c00003a5003a1161900c86100c408081c2c20045841007940c11680360002c01c101d1544d0010003101001c03402c1c2001640c81f1414144280b55030b003240c01000c605801c213400c0c002070b20f80c8801e8061240c3e00a940f0000103407501d00350050351400d00e01c0b41154803070720311100324045801c0e40c1c0140100800c01e84c0000f0145600e00c0d603045140c204440d00303030040c2c0142408106020130320002d1941100000000c00407181c00750307610441400751103900d81301282d0f1184040031988040040c07802183d041000c84509181c4a0f0a103580e550004070858000d0180c8402d6550f09540044c580c2c1c066400100f4407070070003c07001c0044a07140c000400c0c600900942d00744605120700003104d10444503c000101032005220984101d1170f00c03103681e104031032a01442d140740881d064840b090340d00b0b5641c11551540c2411035402c0454100c6042c1ca0400d072036510344840c070f804041d015840190610940d03070084a0f608140250b80c02c1900440462015125482241941041c401c100440c1c3c40b140302d0806 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 741451906 1250 741450656 741450667
    0x7091d011502150a06030c05012d031e0c03060803030112060b0103020403120c02030601140a18150609080c040e03070201030507111009111014070f0b0405011a0f180606 74
    0x1038010303000080d21310704800344e501c03281071081c401c01034180c4000d08420708140c1a0501d098008c20141c0703c0c400f41e807100110000d1601e0030703900c1c42600300344841e22800c13500c01c080c81c000040c210010300786070010102181c90007100044035403010041e00d04890200c40040480ca00b2034032031101800013165401e042603402c00c030100000d61070f080f90004007841a40d800c001b90b109807060500e4a007040c0c1140704204181008500da03507131121089400c0d00c0800180c01080c0030040c51031000380c102c0a0701034645100d07010b40821440c1e0702c400c122003241e000100300d5071010440d034140030450b40482021901c2d60010030400000d0b5000390004c9030001102e10b1314003014890141640d0a02880c1000d06950b00e403102c020500344010101110080c5004699a0071041e01c0e9000281102801009400e001400030440c1403d01011420303210083e0b4000d54200d0882c031f05031030a1802001c07854286050321641d580c0355811402c00c10b4820f0b5421401500c1c8403205000204161943300e80240403ea10042c00c004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 741453156 1250 741451906 741451933
    0x140403080705120c0c06090c0a17160b0c12030403081f05060d1d0c01050313080f0406110609010903051b0304120c03120f0c0611190807091d011502 65
    0x251250130345445098513042007910403410244044d081410507032190345181000d650301c40280f42214200d20450780d54840d0075442e14200504142024941d40a000d00020210f12076001800802503202c1a42c4c03c1405109500c245401705940241c002507602c40001d000c020380e1592242c00c00280340b061940c481d40c52000480740e074031188031440b001d902c550101e03150281d00038610b600011204041d141100f1040b000070010301005080e094524851030599060212034021a00c2d00098100800c0c0c0e00c68a946000c1e0103240030501107140751082c3d42c0042c08104040c410380c2d26541d499560b451400900300c0d4050380d07080d101c44443d011130004000c002240312100da41006014440d04507440d06c5da00e94204401000101e0115209002c43c031050300444660041800c0c21050b801300f40082c51881c00c003068116801240d03035410401d44600c102440a58015144610856056599084180d00c1e4103188041c658005814195400c01a0051100102c05450510100c10510456110007840c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 741454406 1250 741453156 741453187
    0x7020105120c040513020712180f0815160c060e190605090d0c0302060406020d091a090607020c01021c020a1a04051e0303151f0819140403080705 64
    0x80e002d4400c0e040000b0100098104046020403d10840c0b80440c00d09a0548a451000c2c40d940d5041c0d00304a9107070241d03d500103140b1020000b0f8040072000189039a21071841c1c9544450501494800c1c044030400600210340359200f40310001059580c2c04103071a03003582c17044e01400f014030261500b80205c2041140000c0170a20a130320302070103407202040a0070f00710b00301410140d5885d02c0c00c00708a2050140c002003500050f0700c94110754041ca00599071210034000c20020200307688004c000c58854000d181080c58403958070b0340100303541d606a0b2056140c211050303030350f01a0351082c540547c200200181c803125440b03903041c52444041c01610030300d13051540d4510f076034440d6080000502c084003061005110040242448140c003807092020360780160010555a400002d04c1e1320950740301d0007002d0307281d911522400c140301d064820300800301820254019003859400c551840301e5807600081820824014001c8044580740132024410f261640c0e181107032010b00c01000031007482020041820b41114a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 741455656 1250 741454406 741454411
    0xa0b04092102011e02030a060e24040207020405040803070207090b0d080f0f04030c0602120301060504290d0605010e03120324190303081b04050f040f0f1409150604020702010512 78
    0x1d000c0160f90380f800e241f01500b1100283c03c8007074050043c0040000a0b60841002c06064407d200500c0d880c028480016003c1e11901e003000350014102014070040040c0800a1806500140c080c0c41080e500c41801c10111116114030b103500484075060a000700b2000320060072103c900344456450044600300c20001c41e40203a204441c00e03d00300c281000800e40c1800200ea0054101c0440341c59940f410000504a004501441e40c0220300003204110040c900008814200d0720014003948410303a0740c542c0360050040d403003424082600b400c1500068a00400c005e900c220030202c40d242103131140c520300010201688031806041c0100c040024032940c820340d03418489400095540226819454000c00d45072003c0c0102800101d6240c2c00d24000301c003507003550f00340c0d4025901c811b404a5000700081c090480079130340d82071076450200c1802110100e600034086482c41080e1144081d1500f0000ca03584072900388c200c2e16501401004100d0b54a041d4000305190750052421b1400c140e4080d0a80422a105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 741456906 1250 741455656 741455711
    0x40e01090b010e0a050601020606010f0e031e012726041e0e060a032901031b150e0d0f121707030204140d020105120903030a0b0409210201 61
    0x100d01c01000340d040d143d9025648040030440a02003410142c002070361360140540168107010040595003601c6210307651004444000904480803441100d105c203002403414421921594205104010b03c1c51140300d11881850702c0c0c54600c0404145074035108050b0000f024614202100c1520340480c1100c0c203405800500b4000114248074561002070180d840d10359801b20b0b9100020b1402c11072942d45120044c0210b940140707181008020140400c1000c21044c1001000e40011070004003d200d050f015803011207104108055401b629580d60b154910b60784400e0b03500040041a03020058145900c1c2a09040d1040740e1404440c10300c1d985050220800c810310200160102c04140c0c800000904102e402c858a0704045181608100c18810603070304129105008016120540045901c16401c50700c02d81d4010a044004d81003080246c0d4072980141c1e103d0007000e06148804410386400e2040740040c3e83c0c01032042ca01c1001c08030504441c1d150b4980680709655072040e40d50107850038178000b503040c2e211 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 741458156 1250 741456906 741456923
    0x40b06030106120c0915140910030b090916170a1502030403020706050c0706110a0210051c06050d0f1703070c1b03080a1107080a0b04140105070e040902040e0109 71
    0x3500d640030040321440d83c5134000304a82220108201805060340708000d90940c6880000ca6000c0d0031100311901c1104090364111004943c14116035615074002c07104104200c0d4005031603164440b04239510713000040c40c2c07011410701603010080c110b41070300d07200380018490b4145c8450283c01c0d110452a4031030050b101e40200d80000c200401c01d5030500400c800307040c082c1081800e00c0000c006040d500c003664003a88040c081d054070340c11b031081d4080120104d020781c0100240300081202100803c00c0d00314100d000d00c0c02e050500f1420b84001c0b103009002c240c03200a42607c0711100c640e00c5288031543c9205080d156603040440482c020f6019000031841119161120390b0038001d0361502c2040102484010034034035507050420b00005040c0f6003241c081c0310107450310b41c07a042150141b043c104103460f803040c0c09a00c030b40c2c2c103150204200160304034450303805600c15400c103040414203182611001c61b450000541e07484409c143d44d01d810b1703000d00c1582e40017400005100e0002c800c0c207821242e2403041a1070884 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 741459406 1250 741458156 741458177
    0x803040e161115150301050108032a030a020d08010f0501022107020411090109090516080c0c03070302070603061d1b0f0c0705030c18060f010c06051513020c0a0f02040b06030106 78
    0x113191071440103841c40158004c01c486e42c5050a996100d004884491120100080d805100017605e40b400c0100d003040c5101390b990300d10380d90001030750300e0400840c4580803644040001030000a2501041300f15481a000380c601d07030001d03502003941140c05480c0076030440360600440340507807194070680f001c09021400c5c17680e44d403078280c00240247d12161b00959015052004120840e160860313012000100c80c18076100135210005400c05602400c845102d461001084c00d40502d98002130801c119003082e102004040c0d00c4000c003008a030b40c2c101d00d4540710340400d00400d0a4007a0729682411035188040c5060811680001c0c050307203580000091240b03984424010310180c9824082c100800100301da5031003d0b10741c0038a0f0300c5691000101194802d01d6601c440311610707409046000303220366000c0c008201528241051601c15100c1401150103011001d8580165040303034421650801615802440c080c4d01c3c1c0d9607030301a82c503213a500c126002a15403581000d40c0d103445020318060b101540351007217103e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 741460656 1250 741459406 741459421
    0x504110906030c1c02010203040515030109140105010c030e0604180509191e0615030f0311030c12160f050304140f060301120f170909010803040e161115 67
    0x8400500072034402d4200c0030307078800d00d980c869403c0b44c425507040c002c2c4003d000803400181d007140143d50081e50042141055807803a00c00050055068034410041080039070f17002120081c440409004140c0460341c84100b50021a004d10f05039031024000230812403030907895101d40d0044d88800c4141281c407648507020700559540500c09100c1200044040c0f1071240d903ea1600003200c5503842182d800100951580c9040c42401e0700819124800c0203900501c80d941c0345480510710080300c0059000a041e8010080c40c0040842140c40c1882007000900b01102c441c40c000105510040c00080302c48a507021503400110845201d02401e0b00400107192a20300e801381c4160090b2510b54480d203d28144130300b06005560f11405d0703e05482d00d101c00c90118030b800340b0308410600c9400a0240c0703901503819194030303a24206401080d8450381501d840340aa40d84020b10745d0b80e4021806400440c0e05540001502403c0502034903603110b0140ca8a4410640d0a001c0340d814242e44180b00d402c0703096054100f0929 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 741461906 1250 741460656 741460669
    0x1006031a06010207231906110a0506180c040e06060a0906060c0b07030902041b0e010c050a02060c0703060c050d140708040206090a051806120a0506010501080a020d050411 75
    0x401a035400808458a4070100007501c40401d40518600c0d0380300b0804400c807074481140c41004100c4054020340036140200700401009840703124000c006224440c0b030510107034003c1405040c0c0c5034030000804040e2941c03403180d1000c4020202e440780b03a103d2075442d0701c415903540c0074100c00c0c0c91401000e4200c1d41044014400046802e4104484942c100441002980c3d40582e80142141d00585840140e89074604100e010b40701100c0082e50050074500102080c14506103250942c0390b032900d0b0307100c2698504c001901e088444507806041034020b080c0b18005400c2190060442c02c2d84e04054030300094607540c80000b1604444521030003d400030807144104a00c0c0d100c0c640c0c03050041d07010300c8101d1628007001408558020f000a020f844041041138003a1504460342001c2d2800030055040d0780c0c11050340e460444e00445896110300070342d41c200d0380d68040c0072528004071038000c0050b000c260b00340b00c01500c3d62070001e800e507003446a08205488503038805100b018003880c0301e01110080003210320104280f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 741463156 1250 741461906 741461933
    0xf0209070807021c11010e0d120b0a090f0e0303010807360905070801020c0c04050105040513030302090d0b01120201080c2a0c09010e0103120509060a050d0905100603 73
    0x1482500e00501180b6600080d4095031002e0050b1a0503401d0344107441115004600394084070a58241210100c8120300491003084002d40b5036074200c1080c0382d51144009a9080c4180c054028651581c01e010401b0300340c01180d44d1101a01011034203002c0606024a1a44240e0001c5883c1d00050424081e803020b8544c0c00c162842d00e0b0261816070340c50900c2420303502c0300720807c1d1881c0580e03c01c208420040c041c8801c00003811440002c54491191f00e8443c2d44036910000000d00c12440e1070300104007454035115003401200c20105601500c19155800d40080d44001c0f0380c25030100001540b4800540102480d60180001141c4401c40c20002e01c000f4081c808050810304200100744984641d81120464203880c0d01220f8921807404070600741a14100781c04044c102e5044090030001151040d540c00340c80f81202c1c491800b00001d6040e07200101c2d124050300403031903403150081140800c22803048002c1d00140d80015000202a101540c6151800481c1d100340d07840a03440b00010000d001510781d0144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 741464406 1250 741463156 741463171
    0x60d140a05010b0618010f170702010c020613030203160c180204090f05061c140f0f0d03020c0309010819061707120b0109022d180d17030c07020303070f0209 69
    0x6041820001103100e0f05011a1720181c10001400c4a84508500c40c10304070700b0f003c0c0c40d40840c1d0740904140b5002400703081c682c01d001002d44640303800315009026010442038015016800743d4240700020b540300d19016a24003080e50005000350010802d964809020303141014507040050b603ea150407030b2401900c030548007040925141404000c81920b991a0030019140b260001420120030f0b460240c0360b009040098410b11301c18108070042c000303c00909600c203684000b048865424000a0031410380c400c5403440750060b0002e10603503600d940a14112500300c000344008178010041646e54100301c07a455841a4102189004040364030281440020040c082417030301c80500240341c1d1100082e007a0180300d0410035550000b06071035070031854110b6031031040e602d0b4003500024003058800c1107603800c40b1164501080c88100910003514083d82c51501c80e075402036100100407001d0a061049400c0205501c103407001c10028100103940900c0180801d900c0f9030801f2004d1700540c01440b1101500600e02c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 741465656 1250 741464406 741464419
    0x827010f050c0724020f03010905180303070f033809100501170c07050d05071b051f0905030d0504080c061204060209310b09071403060d140a05010b 65
    0x42c0400c03161800d03050228011036041c108131450180200c024800c1e020381507030843c00071001090242d05504044c0c0a041c44058220b00c2f0910790440548a00c0151811400710710078216076039031540a038010f55803a040c64200f00c0c12001004c090303012031b900c1c12800026402c080085041c0c081c5041c0d05107540100c1c0310f180c0003404038101000a45030318012071030307882c5150f49400050b1546492608171541154004142c030151502d071900501650400c080c100c4801060745c212444050400b0380319411108001c104210414003841a4a0359200300d003401ea08004800d10045607603101004106d444855540d2441da9403841c1802c442d080c101010310023407007003404101d400c40030704018070700d250403036001940184d0760704010700015140d0140c1040e224180f00d01100350342c441426664000a0104250011700c0410010742c00c00419950484040000c039003441d070880b258084000c00b45522100280040c40101e00c15181d04602c110140300007909940840d003483e013081020b025021000d40b081e11366 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 741466906 1250 741465656 741465667
    0xc020d060f1a1804060b100503070e0f150d061a09190312110c0a0603021c060e070c060209060f0c152403010b0d201507030827010f050c 60
    0x200c440f0300300801c078403241c100d160109007408040c3d40b00c00038001000b0800c1705015040c0b0000b030416082281e805000c541c41c00d4030300440d070415044031500114024008040b04986c0f884882d050340080050300b010301d07580c0348081500344078801c90340020200440c8203a202c02030841007040c880642510004884600ca804000183c9041080c1e0000b4501e8101040503814441c101e500d4003900403e02c60703001c82103038000a840760b0150b00510b082e5065a80ac003201300422a940c02c2603490902c0b48100600072000000c80d414403848101130903e1080d071003d0700e4040000d00241e0240c100040c5da80640740001b409050308041049014103c809400001502d803030132903109030350981200d0200b20329084548040030360307035420350045103001d034000c000e4645aa142c0c2406a210340c1d00c05031055142c40701803c0d100a9142c4049100784101c48090414500b01c1156021a00b034480036248649100228080100702c00069070150340c000301c9071000080480440340001e00381d400c09880750502c40c07400c214 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 741468156 1250 741466906 741466909
    0x20f0a1d030d3f05041a01060c0201030608030c07140112060f0618080c0103020d060504140610140d0b0109030503072108010311091504020c010b030c09061f0c020d060f1a 75
    0x70300c100100c002c2c0b0000104d03036546040c1184000c1e4000000e801c0c1000300000800c0880c0c12844019499001381e90400c849a151181659280710301031020300c0c20f41c4100020002c11041c3e1020380c494240614011603485c0c031502a0005a031704540115000f01010a010701035264051413040080700c03400228407002c3c4c03800196584540002200c0c50406400050307140d03800b00320750050002042c016008002c000004410051594810b6907400c0c031030a540d2a1030f00510344156031141030303140c152000c2da14140d0b4200c405001032001807a0241440811300000022a0090010b000c5d10b60240329040b840882d06080c008a80c021280c82c202404081c40046c0041a2030012000005005075201d6150792116000601c00011078040146c0c010700010310814580b0040d0000844400242c04031404038081008018444401320740b50740d00240305034010859594002401584807800d810000c1142c042500801c22180b240c0784c0a444464590380403085080320340c0b04500d80c0c50078201800d01403084940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 741469406 1250 741468156 741468257
    0x3150601090b131d04060f0c05041e0e01060c050d020d0c060c09050307080304050f0d11130b060708030103110a03080f2b050402090a020f0a1d030d 65
    0x103400c0151004034003d454507441c1c2d290680901036500b10009542100c180e04c0c045220101c42c11104241081110b6802c0341003800f50160511035501c1e041c1c203050a02c81805030f038010385040c0c541c03101848600021210143c4010724041c0502da5910381418500d803c00d1440c02c0e5084900e4811980811701c82114180d10015225060394042404a8540b68981e022110301440750041d81c1e050083c0c100006801e00000014002c8400c280e800c00ca05009100400090701d0450b807028183c40303194620740f1507038600204a50820b5aa80800003185203400d030110303034260004401103881041c000018400d00041070300b20440104221a6501441c0c00c3d0358820919005810f5050448180402c003510301c441d04085840c00741d0141040500002161030309180030700313010b44041e0301070445040885c1035030b420383c02100c0c0c1000400302400c2c0380c502030b0701f021280d504070107100309031980d81d4246000d466902403045d02c0d0400019900c89d07040072007003031346003040c42d4540d030640390420700d0b0384500c0c2e58032942034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 741470656 1250 741469406 741469409
    0x51327050619090605270705061605030d0c121b0c080901020118050105040b0f282a030506010c030915020a050a05010f0501051c151d0c0315060109 65
    0x180310100d0100c2d01c0c0d100c46000303402c03090f000070701103070428040141c039404c1141c95010b01c0d00e840360748681071200054400d440d80c259000303071504100108080d03c886002e0400d41603000e842801100e1410540c0541320040314442c0444030001034003007000303031184242d070700440e680700340c210b02d1030b0032501c05030075000d0641200800002c10070040450b03c824642e00030b6105044010f05140b01040b04026440d00900900048500b100d4101b800e0300403c1c8040c40c4410700511840c2c450340c04859046038001184140c1000444003050035484000701912203403400302040d100c51034010700c0d010034400038070090148da01c004c0606041209003030350780010039403205544003103503440d11440b4a2446100303022410030310303800400740c1148a003681103070402c04154860350001441c01010045030341c0316070420049000200e03401611542480051700070820516070154600c020183c00a0180d0364658a10b041d0030000c801e41c0c410741c1140346070380818141440101403022400d1900f0f80c140c50001c0018240d101c45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 741471906 1250 741470656 741470671
    0x1b0a050a080603101802042409050c13060201151a0403140109050631081206040b03100204140604210f0c032306010f1e0513270506 58
    0x7520206035240c6092207090034210140d5010300240302c2c40e2400c1540d000051008030f01981c079026221040702d42c1c0460121900318804040c20080d86012020400b07898040c20085030044d040021343c0a400740581541c00a104a400201c0d40141c0100201000c41850388411940303050000c0d152400c1e04841c0484017601c1c2d00c10003001440040030211341c0186210b01004060744200c4042c031071352918203010324802c002c007041083c50a04000120160315005070500520444040c40011014807100c40c54581c0410050300010300c000100c00020300d000340080014001c1940090180b10703c07117940d10b10061403641900d0b0345107010715010b200100080c060100b0405015580000001c200e18852103810b65a044420401c2c074603264280070750090415003554002405d40000c040185078040b0300d00b8102c3d01c2d000e22100c00303d41740c00064074030b0761284140c3c02c1880f803080b04003060303a40d00c2c0ea081440c80310300c0c6080005d4401000180c0311b07081c0000500002e851090b8076011002a80c00103103194450b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 741473156 1250 741471906 741471917
    0x80f25050a1403070509030609070e13020103093002060402100e0604090504060506040e1f0b1903050309011404140105091c03020a0201030513030903020d030c140102031b0a050a 78
    0x3688442240c20001842d2886a4414000180b002c041e5004010b00043d101c11400d0715035070b0710381c0c0d80c40f140c5ea4101485118000040f41000403502034403000070312007190042c10041404042aa9880180000c1010003d0320840e0000c40c980000e00b91200100340405600040065040940000d142d210800f641203080004c0d48036006031540b07500094070000d00001e00e00748418141480d00030007070101240d4a41c001d500c0d00701040351200000590030085a416140342500b02c0040d10304402600c000105a0740081d4003104c00c0804c000500c01d420300a50199014540700c510300400100804c0348500500d46550007440b0611500b5044000203180603024280300d546c68161030042040d4414180d113600070640040014414190007207400c00080d4403d030b81c03c000950b20111944250006543e0180000740e20080910050400c001d0f01840b6900905003082c1c49002951010003a08201c3c00481c402d03500031081c001c42204850b24550042003c4800508080303008034024058001e18500004110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 741474406 1250 741473156 741473167
    0xc020c06030f0a1407020a0213051e040c05030a060e010b0907050f0d150806060414131403070501181703162f03040f0b0405310c080f2505 61
    0xb00d8684c800d1010b00034454105642d49071142000e505d070441500160302030340240c10182c8c0d80074510f110321841071800c00c20410001c0c0c1074071040c02007250300030403c5402e0780005002255a9404000c42c002d614880c9902085c00004a01120b003134400c1c003900540107a1480050004881e004015601c0c0400501545604d07a240d0031900d6000d0401c1012240a0100995000c03d405402240e040e01c180d00588081c00141c40440408070317900000c64072a0055001003403e01c00044801d51690740c0c010919007203a04003542c0d515000d08480c2d05180c04501402c0f840c4210041100450107102c8841c4407000007415454080c02042001914030040410407180300040d14240c2410305407240410207561b0480c0203e074642000030703503d40c01801001e0181c000b011001035424500001c890603107030058074402c2e400003035100451402049510b600001d000b4442015406103041c49244c0410041d03a5988256040c80b0100c81c400c0a0080c00c26483d004504d44504a60780e075207403c0b042c00e080140380490740c1d0b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 741475656 1250 741474406 741474421
    0x40501080c2514010b011d0103090f211101050609010e04021306090204050a0503010e03070b13050604050102040302120a0c05090a020c06150a120c0b0304020a0302061c0c020c06030f 80
    0x8081400c252440844100c40c2e05060140041d10035810f401c3e202c008001e0b02c0e02d4180150713084820000040003410042290b0307202075100741c101803040b41c4907492510340c064941d0b50f0340e540c40d101229207070152401c1280201c7c5d020b5002034100950000040200300302d06200010030003042c414029491001804004901151558a00c480560200351b404200c0b01e5100c9410030003035801441101e11170821040302064501e81841191000ca03c03d5000350300c0c1c59150b954142c00300c4001007103c4403800c8041704c6440845c07001c0c4280b41c400d601c80d100060f5564110b02c104141d4030000e00804040f54003000c900000103180d0203480059840480d0400707019036448550340d029109452102406010704000c0c84042e861004004140490495904603520f88400640c4101c14a4540190950030b085404100703801801c1d00454105002800102415071650046081c990001c805460719514203d440c0f44920290310801c0c0d004d0407203101512548068400242d0303e03020203010781060344104004111076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 741476906 1250 741475656 741475687
    0xc070f0807140105010503070b09030a14250602070f120b15030304061809090302030a051305040504030c03080a050c0a140c07062003190f02010e060a090611040501080c 74
    0x4042e8801c0c1d040780311440d03a140183c041c000a1082c0c6000b4404c20002080d42560602981c9050308090003d100c00c50803501d450240200192400c050b078002c0a0240100c403160321040700380084280e4000c1c00e56854008002d280519542c04010010300f114010721050004200c0c0f425850340100640c0d5094580d0b002040d0903e20000c52264548400180080c2460b00300c0859032601030700c404d015104d15070758881a4240c0c0c0c0304d0f010040068000b0040c2c14001781c000c10203092228184420020a0b944079408101260020b45081d000b2a801403284820141c0c0407907585d52000907943c051041d410440c0503140a40a05a045414012139507118090405c0350000c0d26064503040044071581030b40e84c01c015082c1d000c058810303070f030210700c0c2d05522254800000499100283e01d0810b88003611160104640407100c10401c0011035484000486101c10b003044858014080792800080f001001c0c81c2c4941140c1e800d030407940102e0003c1c401008a6a00b00350341c107900031120b40c2c96903920081d80d0040e031403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 741478156 1250 741476906 741476917
    0xc02010e030705060414180403020a12020703060204030303050a0c0329060f04060302280e010507050102120907050f0a0b181c05031201090902100f200a0302010b090c070f08 76
    0xc0000021a0005072203048546030080168161070b00030813818847c592401c000700c211405009030340f010704c1c405d0018501d41c3c0081015031145c419a0101c5449540c0c040c2079901c0b6600a400103a140c8003400200c0505100f0400c0030306031402c1c00c000f64240700144110b05000190100034040046002c0c1c9015113070003017226010070060031103036502c949402c0c001d0001e4200c03003e00f04a050304000000d1360300d00201c030080144000c0d03450300c90620459200469407a07214090841d00c40d5024420000d640c0c02e0017901c0b6025070741c0c100c09401220709210030320006c064406910740c4258001c3c80204451052001160122440802c202d001e820000c030108240003407000c030b0000c1400e031f0701c401d1805004002c80500707910b11544c03189207402d90340c85040314290365049038040d5000300c1d90750240482600422072421200101d00740450880840111f0555640a8010300e5883da0400c01104003099420301c0b03400d101c114111031141190411078071420040c050524001c100c1204814420f00b800885804d503032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 741479406 1250 741478156 741478159
    0x7090911070602040308040812120609041502270102070e1305160608010608100501080a090501200c0706030e0303150301020f030c190906120f1506020f0601090c0c02010e030705 78
    0x10342d03c9a8a2800070710647c014428088a80070765a003507005a0035020880b150b62440184190b0f0a0300d40030f0811101750380c0030b00100d5000f84a8601c81d40260080d0000e44509464113038411580044540002e20901c4410009811900704c8101400444074880700749410405924414400c2036903031428034604150003c0c820307a401d000c91800100168481e1034a4140c900315912000a503e035018038402d501c3c400d000325404125254000707481e081060b4410900e207801380002150042008c140300d010106240d5030b5046040c00007640c101c4142e42000b140e801003140345020420b00005216141c1c6a0001400681103215100c94a94075990300b5010380700e4180c00d6407540e03a030b06d0901101d0095a58421b030000300100c1c20a80c00d000340e25000c0c1c80c102e800c43d6004d44400501c0c00200701c00034000e094146207034564541d1000e850704201c1d1055041d6026103000e40042403241842d85800b4941441684130001c010304000c3c1c0558416807080524400903420f0800f5030a104820700000d040801c550800c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 741480656 1250 741479406 741479411
    0x120b0a0305151906030b01030b040c050415140d05120d020c030f27010212070c12050115150e06030408090d1101090501140910021c03050a05010608070909110706 71
    0x2084880c0c0d511500c01c0c003c48056001e08145202407410340c05448151102034a030110420041010441c9480420f07402449000c0125100d0b4850000404891140c407000351091404842844000922240e507070420000711203c107540101035944581c4c402101e0141c0d4200c0d400403d000c4607050f525015500c1c00082e000960b52140d54005a0300b501d5044a440e042c06580031500201e1080700d401d140003c003c0040c0d015000400c910a6180040e40c046079085584940d50a00054122440061034806511680001c82d44031100104000d0b10a02c5820540720304a2407030b6803070b400c160865a640e04029007601d00e0340d101d94581c20182000c4c00b0710344403190402c41140c9440c0800c0314500d862415100c090700c6600c04c0544801c01120b2142c0e021004046004c0e040058880e03e00e003264150b8540c0500c1e1040710030f6002c2e415845030024040c805460082a12401400000c3d48540078036405440c06107003440e81490200710081010005228000f503060f82d40c0044c0c9a200314590032958642d800400a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 741481906 1250 741480656 741480673
    0x3021b03031513140a0b060d020c030a03111306211a0301150e0a0f060b0a0e031506090a1d030c030712030209060f03060a050414070801090507120b0a0305 68
    0x714000c404032580b0b00c00d00b8061803102c400c00084c0324096003e2115006528183c0d15902c039200104480d4071034a6103c0b1050000c000c29104071700007001c1125805010b192100c0d1280005010f0316124036031041c03816401d000c40c0c4800c8500850300d404450045c500000b002d0035100e0400300780b0781c02c4086030404c141442100c0c0c8010304001c41c030036144c0c0420f800820100c01e48800c4501c00010b540100d050b0301002c4d00109822072480e030004a031960000b640050200d681e981035018580c0010841c2d004681c22083c41c0c0300038a014401400c040340b0710700d2000030078078000e0000b82801c0e030003d03c14010160760b9200801c8461440d614500485400e20032280c0e203d455135a002d5030780c0c0101004550008840074401c0c038582c400c0c000d880c1d000e403001d00844e042804014142d00903030402498250820310001c00040c00360303111b0154624070014090050717a9800c1c0003a0050a210050700f204507903905040074040304c2c47e8050fa50300c4110501c21000600e0a6a840014040811540c40074065215030030070b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 741483156 1250 741481906 741481921
    0x80d0605090a1a03070f180e072c06010c030c0507031202030d0b190b03153c011b06060b030f0711070b07031413030302010e0c09040c0603021b0303 65
    0x440d5042031055120a40c10701036950806503107103103d020390240303041101d030200810982447d4202c0b0304042414042400808260480d1030a4403581c82085800740e040807200c122000e10040b1082e24203694010388191825000117092908180c40081c2080f0040c40c191080c40000d00c03c0343c015603032000c52182e2000c00950002c0da41c0d008540100b41c158070b04181c840c0c4034505407000303079110481031203801c10700d81c9455085072064000400410a14070114030546459440e1186505c1d02000394809940d44018201d03214130041c08010002c80950006042e4800b507030b0440210b22a00c440001880741c001860310346600502a9a0f0142107025404001e0204d05c0f000754003110300c9551a40c0e01d1007020032144158603520000d9209200601c44101700c06000b080c4134960451117000300c00c0380e071441c05560000325007801c1c040c0c0e44140c0060759665080703505400103201080010508452100c01400c1a4a85540b5640c031403240d907060560001e40784d0398101007008100000c01800b03003500d03100c2c0342013607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 741484406 1250 741483156 741483161
    0x1b05070534050d11060a230712050903060a0c0c0609060203040209090714042c010e0f070f09020309010b1c17120711190c0e090309030a080d0605090a 66
    0xe40c2032070821a040c101282c241814212901c00c1c030340260042c2040d503100d00c24000d059000c00e403820200541c0740e0010124496003204800f00b0310060040c0b80c1c2c1ca8125080c54003032910301040023020030000700300c09105560f0025601e904101ea001d0b0000342903101403c20348020600300c0c0d00401c1c40b410414040d01788030003503001d140b14034029140c92086d81e5030000800d449504a0281d281d0110b0503c822642e142840d03480070180038155071840c6507070720100756002681801300e130222003245c0d1501c0018202c3c6009104030810300c5401e50040c0002410f0485080c1c3c41d4009004040c4620b6010002a16028094001b8000702c0c9002d083c1503044003080052602c41000c095042c2d03021400045011070501180d0b013160080d59100c1112812915040e00c2201c1c81070308901040e00d5449450403002d001070310100c2c681d00740340c0b02d440011040303441e161210720190030061000312250000d00c5a195141c40100700703140180d0b4042c410641d503032210b012000040c00d00381c010a42224600303080040040043c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 741485656 1250 741484406 741484483
    0x3050d201603110307030201090e0c04260d0305010605090409050c09090f070e010b03010509061305070f0801080a02010c1b0308042c010f15020309040c0c0b0a1b050705 74
    0x18440c07283d02c00c0e80d05090569400c41c52000900040d203808041141150740180b00b0342007200b901e1800c0c5459034aa2151606403c0300e40441c0b00050500380103061200b081106203104400790805000395071400718050301a006005040380119102c00d0f42c0401c11006101c0d0030f8040320010420310032401c11186e070070350b1040795549600c0e1794807075840d001c11440c840b5000c82e41202c00c00581e40b07103140e0900b428400802c0c000f50102784c201d0f810103004490304201d402801d2155545688080c00d181c004c060040040c00d0603440324031660828943d90f07000d40da0010f1410b0303180c2d0300301b80c4030740207101d2088920641d4141c651000c0d2845402080114a900e402d1001d0104a000c6110700c10700b01c240c1450f000d07440d400a1050300541c2083e81810844003649220b2034003880120b005803401c014030b5401083c1230b5a40441c201c1c0001d42d09507010f1040203244940340d50401502c55040104c210440402440c0050440c220404d01501090100130070034204a0351000c00c3c4048922038a01c2442040d00c000160300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 741486906 1250 741485656 741485663
    0x506010605030f0f09070501050c0312010b09041139061906140f19180203060114120103030e0d0f051f0b030c060315060304030915030603050d201603 66
    0x122000308041007004000280500f110170040c20300c1d02d00e40001900c00d50712a2000c0480d50205100316402c42c081e148249000b40115105140e58011000c1000101c4034165460341204505010310800c00c101180f02504004c00000908000711080b03c440004085648a0304140d10070340e001c1180340029403001d0180e1890080381840300603100e0144112020b14410403a4000b1001040d44c8241d150808800301003950180b15801c480b5241e8444035000c00185090209031600001441005c0d40e00c0130080303100307103800165a802c4c200d1081060003104010700c0702404003c9071155070a1240c1e6105969503090358030410358483e80c402071410688414800120290b070302d242c10100c030070003483c501501e510100010050030080c0c0e448000c2020682015051080014903039040f4502c0d903e0b56801140240d000751160703108145003800b00540e90355803580000815003810303000c100042000404100c00151400c00d01115040d610070410807603103d41d15405103110b04000329044069010010081e41d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 741488156 1250 741486906 741486931
    0xa111219050106080601120914011802090a090b010306020a030f0f1d030a02101a03250501230a1124010905100b1b03130e060906030705040f09050601060503 69
    0xf42e40c0700030707218030303404940aa01003180da420744100c002050f440700e00998070070f00b10042d41203400c0d602c10307007183c4001440900c0309010710289410351078544440341e40110714920510080d250faa0b5110103044040c40010080b50b0041408402640a43c100154485c4460010010b5822140e000710141038201001c00c1612002203070100c0704031009c41100c0d08060b203500201840060750500300d000340109141e05500a0309124260820794060050182c3c03c000c1007a51078510500c085058404401c070f0f40494144400c1c0449030843c9000500c1c580b141d069200d406a481e40a0080c080d40d6000c0b034120000150300881c09222038001c401e58410358021643e014041c6907a8950961408a44050711603049022580b0b034108680142c03040204840c8a11200b1903040c1404461111314580050168584c1115110400c0c031910541c0625503503ca08100c40b289194100603020946416003405140d0280b0b45540d03c501181406400801080b1750000c1125555a0740744030080c03040d04261842c185000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 741489406 1250 741488156 741488159
    0x1507120c02040b2e090305030c060f10050d0308060105070f050304150305101a040b0a0503010501031109010e10110a230f070e062d0f180a1112190501 66
    0x100b0400b24460311140207000c605203c1d10b4680d240c440135052400204001c0003200101c0020310510291041103c8100185a01d00701a401e0a1141000a000d03800044110004100950b1089051154982c01d41850300c041c0d01c5010040360b2500c80c0d0b003409005110803007202c0c0c0400c000000100b0031078141c0e54250034041d1203da01103083c1c4109540b8a00c40b0001c0507070510010310b03603051140c48480c1d114900e901e4203aa820300c040c00707504807400b42c1e008070340e011004109a58040c026030f0b0050f00c6000350b0074a8410104c0c0081c00c0720019000c1c1d54041c07140c94020380580c40c01007242d2540d8600c00022100a04800d203410500d40c0088080c0e02c1410a001405c80c600d1000059100c11590301e41e0041c2015505000c1d107011456401446142e100180c0ba040401e180310000300303a132040300c040385204620f4a4050500c131812802088003030041c55008251000150a01c001603009005034034007085007000004249503501640407801143d03040c85c000d00c505016031035500b1200c007440860500450703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 741490656 1250 741489406 741489409
    0x5071e0f140f07080a0309170a03060f050d1103070b071b0608040c0b0307200c091b2703011b0314010b0304030e212113051507120c02040b 61
    0x602401412a1104100f80202070004100c14007411400304503140001d82041c3c1505d03140103903503120680341040310001500240082c4c0c9402050b001c4d10500d20080791251504000c00c208070b40640b03015003480c4860260350040e9505000460084c90103524058655040341405d0076400c200a030041d103007882000740003a54a0191016a00c00d54111074407400151034442c0c0c81c17180b1350000303014008110078a01c0c2e0010b400b8006e18642006c84041d0f0003031030440d4564080c0310341c0c0903010f040c425041a20400c02040703a081801158407000441321140865130740003083d041e00c14400c690f81a895400c05903100550800e000301004c800c500c0740d030240071147c400c8000101110081c05090141e400400c00503001c44e0185000c04403144c00503048041c600c082403c00c1408800c0407017540071540094040c0030b82f2000c2c89240030100001104024923100c1c0914090550b82100d20806014220607050b00500c40581010341d80015000701c0c681e0030340c4030500001401154841412071143e480c000804059 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 741491906 1250 741490656 741490697
    0x30603141f060302031915060b0304060b031c030b011206092703051813051017031201030209190216030908011a040b030f0304080c010f021c0305071e0f 67
    0x11a07402a014180c0704201c40c6c080200301400017000e4903100841e0f5580400c140062080d14000d16406001e15160701303051501800b5503001c022914880d602c60701001d1100100310241201c21465410005980307800e60006913600081c1c040350400321031074203030b0008941d18142c2140b9030440900f44d02d002c0c07009070007490f2615211044005800600300b0320040c0c4941000c0300b901030300c0c000d0050144116851840c0382000f0b071441201c540c0010380790301108002200e0340101008c01c1002082c040c0d81411400c0c540b4840b602c03414840a4070031700364a80450003490620040454032148410103650381c910b01141007030000d0340c442045000032075800307000400101c184945510700b850b124441080213441e408000103020041b60595145c020500f1020004404100800040080030080c00868449000151420712801c03805805d6410118102d0b1050001d082407100380341250a00044640b07035004202c0390380403061084100d07900038140e90f250494024001311608065651811220440348154040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 741493156 1250 741491906 741491909
    0x110a0809030118200a03080703090e0a2016080c0705090717150a09150f1403070603020f0d09081b03090a0501110114010e0a0c0c0f080901030603141f06 67
    0x450000c85589540d03800c0d4110701c0c4d451905004114039591502c0c6d84440e40f55900016049000c11040c100420903500c1d08035090758003c151100400c0000c0e69440d1210000041c0c1e03071807040d52500014035441f2410404505800b5071f400284240e2598104074445545442c18041c05100c1c03030403a000114072030b12071490518441076600c03e44440303464501250b0200d020413251560b104034403a0000c00c400076244115210710201400f050b02c807070b24003c4c403c0080c2155400114901300001800040368600040c0101154050318005076910b003070700b441c201c0c14040da0040d50740341410401200c0621898801034511030301d50b082c880010b017200c0101c0ca55603210314400140c0000004104001f00d6000d00828000e8510600004c50081001c20322107101c0ca41c04d0f045582070700700040c2400b00403e240d01c03446680000350308055503419080d85800440c5043c007030300140a04000664180c9a911903013026004541c0841d401680020007070031641c45c6e820004040311b13400d80407003250040e8012405900e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 741494406 1250 741493156 741493163
    0xb010f030b0a1e0e070509070e2404120309050411030a05070e0102120c07090e010c0f020a0b2e090c02160b03010519080a050c0a0803030f0a0c110a0809030118 70
    0x2240f400100e01c034040a00070011100380e40340074900002645480380030b0f0f103a2284080b607407064485401e1f03800300300a4401000c00418503020024040060f85009011601070303602004d50540c50a05510b400c59a00e40250403450b04607040a460b010b18030100005103004400301103091110782e50f00c0400301d4030f140042003002d0040e03001104030152120140001c003182c040e484207440003d52105a0802920105407205410303070b42d14100c0240c0554407000042907a8a244050017907a100c54940c41d80020020303001c281d030521501c24002019003080312403111500251030004019666842a40c0141103040400c40540101c0e204a10307840558121113040d06e845ca1286070859080400f400031050703d4062444c0000c2e030b0901c0224100da0100421800d2138800c500070031350890100d05015800d601c86e03010603050781c402d10610046415140420b6405011000002038060940c130085030244020300111001c1d01445d1001800c0c0706d2000b0050040c1c0d0010f500a011090802e507155000210740382015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 741495656 1250 741494406 741494441
    0xa0c09090606140312030a0e0105090a03090608070906050a091d06010806030705030a08070c0806100f090b0105090409061b0c0c0e010e1303030b091602010605010503010f03020f06070b010f030b0a 86
    0x400f40c00f040c0809590071103240c7c580003400c2c0b54110095800c482c401d80d40311805c0c0d404145c02d030080607442080c3c44098007840c0b400596a041c140806049034540f4040c1000340140480c00c50350755440340100300300070300400c0b01c514403030000001428802142503d80500144c4003600083c514200025050112080600141a2058a52602e00e00d580001300304403130ba035141410000c0d0501c800c122850003100c03044003c1071001c0c9401c0d06101000d0503580320394a441e0400034014156a0400c042e00e200a01c180d8000c29080101e1500300d0042a0340c1c100180b0402141c0520005645d100041c04005441540c00c0c0e00aa5200d140d0f2601c002c03401d1003070100240d0b1990024100781c00034000c61078418843d05000c218049107000042c002c4008039604140300001d152113440c40c0394240110340040c002828014555410200404007a21480c0000390198070fa015007000c3d152140070844498a03000010411656102c023000300e1600903901c0140ca010080e50301280d1008228451400f140c098444507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 741496906 1250 741495656 741495673
    0x10915051206130e0601060f0e090609040c03080f070302070b130b16050a0f020315060a06050f1209030712050f18040902090a150b0f0304080c0a0c090906061403 71
    0x1e00303803038200007051540c200c140803103410011011070140c1c00e41d14540c0400b508680d810500e0042030454410359040400064007492903094403102101500b03c0c0303060b101100550f585062501c01d561055200801d4202c0014015a8021481d805005124825426100c1c0956580528400d5000303030780c919051071511841c10041d481019004028204003064024008416500c840c0e043c00c120382c00a83e0303079540c60064030f0118501406100c1c4084106d031402c8585060520109070501303045d000e0403007848030002d01d044403503c0b40001da440d0f800d4082807540030b80c90400b1009032650083e140403074031544000c0b4000e04441c0158152981d5050b07041d0450300303100e043c51404040d44e05606000d034025540300030601c00f42e00c405003032506c665052039020030490541c200071248401076911452081c00c0502c818101184101c0032607801540200107261288003c200f8141040d4020314004d140c0400003200180442094008000c4070340903140400010b030b80c07407584260542c1000c03101d940c150020100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 741498156 1250 741496906 741496927
    0xc09070e0120060f060a0306060f0504050c19030209061312030807140702011d091807050307140d0519060507020c062104061e0911060906040905040f0804031101091505 74
    0x1490b58841c200514020b000d981c0c07034230382c0000c440c0e05802104003221002d005001c9030030140500341c1c020b0b031012261403800075407480f0b425181d1110140c40c02010f40002d4070f040d017692540b095661004d450807292030f52565400314680041100c0400301e01103500b040010f4000ca00a2200c101000c40140c01c4a00d420165801100c55000090002c3c1d91502010781011240d2100f040f0507200d07095010907420b95150641c003e919002080c0e002a01c03a5003c0c0b03200340304081ca040b24540c4001d40c2900c519080c01341d1860541d040010f2038a0b43e802070f2101c0105603090021b42e807c620700031541c0e6001d850705149041c0901170503206000698031120243d2030303040440e014900907541d015020700400240400c2c0da4000c456034260011400400c2900c0e5494001402010801b00041e0001180e9842c90400503202003552405144034550380c06a842c80060203000c16210002e0045600007019550b46840b8070b064079401c1e6003610301c02c0c001008400049548080c100e0030040009150315480c0c10002d2090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 741499406 1250 741498156 741498181
    0x90c01080f06010c0c0b0304051006080304050609060d05091b010c02060301062d02160e060906131112041406062b0203070902041d1501110c09070e012006 68
    0xc2c5501c0c10490740d403400e0008903441020500c041d00311003000e42d40e41d051505005280020417040a0b21003441c16078100110040041114202d44c001d0752015103031110940060060301602c41c45410f00c03402c000401048880c0491054415603050301100180300005004458040c441500250050000c0005220880c060f100815103840340281c180302140c514281c2038480e18928030300401603403164011451403110800040083d00d041610070620303240a50001c0d80f0b6440141c0a14080d82400c214103c100321035400407406004800091665590141944d620100f030442d826690040d820310f0740c140340d001c003044141c0038082c02004030122406810484115295885480d9207a081c0a02c40c41d0043e1814071402006100318000107132202c0c41c12102c1d41681503602c1025041c82246000c1165110b21700c15030b1400c0380428609035a0317100d80150414501245030481c00d60001c0b0000420400c190b105402c000c0c90300d800e0341c40c0800144545250029054514900106a003041c800211001a040d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 741500656 1250 741499406 741499411
    0x13030b060319030504090c171f030614040623040204020c07121a0601020a0f03260f01150311160f0c14090c04080316030302191205090c01080f 63
    0x4065807001c0300a6551080c0d80101201c040740404c0c00420300304030311303450341c441c800e80c4007101d0400c12031f450a4a00c0c0920b021074001c2004c500d104500302042c0c40c0078589448000615440b103010021010f01c150100c06410701168100c4d003450611044c0484000070a046842c442c43c10750902c80c41d0340300c80d800c0001035001400019102d2049840c005070100280b4160b820884c018880548420242192100700c0d5000824217415580f01705016800035541190306107045406240103084020324540e02d03440c031a810001c080040310110240003c0300c9818410714102c51041606082440f0306070821b500755a00088101c0011400340721100f003480d0f8000708101d41c0380c455400520039480741d0f511100d00031980d4001e45c40b40d4415901c0c100703c505140002c241c1050340480c030903003440d02e0080070380d0b900d04c84c0608204015043d1aa000e00705802901691100000d1038284000c1d4900d5034002001902021140f9190390709200100382e01d10701c040703460b520006041e940c10000e030382c0301d1542006c41c0601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 741501906 1250 741500656 741500659
    0x15030e0c120c030109030e03150c0d020a0504151101060618090f111903060503060c0a0e0f130c02150108191529010809100e0118031701080313030b06 66
    0x2011040d002030341c0c0c03c0c030030110042d11035141c608007e461401413524003035020303c86400300c00d40281480b0070082c8041c2910103601c040701002da0394449841084076a8001d44e40030440e1a066418040f1a01b40c0000400790f4400400c4002c011550b0754150840e803040d03003040454103e1902032000e000d140c401390416040000c8191012400c0794002000c24003903031102065140011075000400c401d80d916024040c0102000c40003418507080c407000082962040351840001e100c02d8440119891301c6044c11103c2591000f4051003150b00103401d110081c1c8154207134100180500c2c1d0721015004148154207041c1c0720504010200d88141200641e2100400103041d0340040c1251100c0c03103100868000c5502c0c010760699002c0308100c28949a80301c400d1500c0e081d60500c81450200b2400d1013000418103903000c50f000c00490743c010240c000900420440303058010180702020000305044d0001d61803c1004540c12a0710350303982e83c40207507036101c0c0180040007074014034062081000c510b8800c05150800740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 741503156 1250 741501906 741501913
    0x3090f0203060406020c0708060105011d03010b090a150501020f0c040c051327020c060f18010e03040e221101031103090c09090a052104080304080715030e0c12 70
    0x180d00001c1ca412412201241c40d02e400040d42990144103115810003032100c1c900902542d4100000a8121080105488428200707400c0201d00c0340c0c1c0035044004600000340c0303646150f050030207a4201401c050300349440d00d0340210100144551002801d0700010039058050458007940400700405000042d440d80200a8140088110546600000d000030700500c00e03102014a412030a10310619031510394000d0385441803100c2d408d102030110304540d002516003214040e81c2d40c0c1419002400d820601240036a42c07910b41d40a8607400000002c1064616031070720400703103950300140c6440f8165813106c1b140340c1c0d003403e8500e0300005810701c3d100c102d00c0c00141800f08003050303410030982c00c5070000c0707481c07025962003551100c0e0f890401c1d0b10340c1608481c032000501b40708100c907240c066031050548042102d922907001c00030b00143c00c00054034090034515042d680e40e140c0d504001030303490307000f4007a4110003903422000c0340c80c15010340f02c0d5550801c040760180103900c03030a20402c085112101c064220f50301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 741504406 1250 741503156 741503183
    0x110318010516021924200a0e0d17070305030a060e0705070b060d1e060f02040b0a050d1d0708240619090513151a10030207021c260a0309 60
    0xc1840344045c540080080001030051103c9909120345400040801081307004100c00c0400c07550188582c801a02e06684883d5900e0691405840c103480e4401c181012040105d407903400c05922034001c0d03005c1c1c2d95003d4240070340ca8944c0740428440c0b0302070b502103006c280308001a07800210429403065000c840141104248200c0d0303119200c0c01251380e085944000881d003120300400ca040e100b5640300744039150f4118181820901411510b215880400c420f1000200d5040200c20954000405d100c0e10a1446591001c2ca0042c140d65250580101001e9006101074000011b5000b44102004c0e07020814075881503d4110521541d680e0720710304002100c0c078190002c00c06024500515005000c04000380d03c0c907e4250501c080e80d0b0841c043c0601419080028410000c90180491081842c040340c0c9810040740a220960003485100b00094105511424038955842881c2d0614000c0f40203003410340d01800c070401a000c07249805d1900d400800d606011004650388698080d090880c86006442c9100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 741505656 1250 741504406 741504443
    0x90d0309030b070f08070801080318061b06090d1803030305040213051510181401051908190209011713170d0606022e1103180105160219 60
    0x42002c494034004a250010415040385e400403000394401c0c0140382ca0b450650401c10410740740d1043c943d820b10201c1c8081c1c0100d03255594601215242612040300e82c000d010380291968075030100301c1e040300f4103000c4c2c22140d014881c001e0702400c0c6500741038021b402c01142965000d030001c19002d44160b03040148918a00c50895452103a140124882c2c40a00f000403c00c408115448a080014404010500c560101310303860303560240c0183c40d4460010a03c1c02203410049450317014001249880020110348120050307001008103028108910f480d01005106003240001d070b1184072480c0c3c0c00201e50507038646024114100040c1c10030a141602d8041941c00e8130b80b41c859032988261303150340000010f0500c05511640c8a043c0080c50180054009a003800003108600700c81c200603d03e60070a00b40707110311420300c15800365002c40c8071282a04e40300e06041d984a1112001100545042c0d8a804040303210801c6070740c0c400c0003401c06640104a2071125288422155094000c1101e0a02200c80142d646 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 741506906 1250 741505656 741505673
    0xd060528091d0a050a02040c0903081e0f0403060e1509060609040302120c06060f01080403080f0c0403060218040f06290c0a151532030102030a06090f06050105090d030903 75
    0x83e030b8011001041c49222500404c81240c0d9000340480c188501b41301c0c20000202054107583c4645828586842d11100f01c070040d46e464442c1c1c000d40800b0f8a00020b0200400809a1110500400315011101944400c9640d801c100700107461f0344c00d0755800140084c0c040d2404c1000594014880d02c10380e40203001380a503e0410b9044542418016044a8208281811712680d00a107c01c42441c0045583c18651800f9008080103440261008401400030784107840c4442160000c50707000700110340c1c0e840304500c41c680b03d41c010390401e0b110358208407901070400a1406510292813500c0b200c4002170f20b82c1886548040c1c2828000020581c1c01d00425041c03500c00d100c0c1041c1240250104d041c0100c100824100311001d01c0407070300302c010310940140402002015003400d640601600c161f45001c09190100e0800c00d40d240d15030340741d03000108010001c4205e030882c208841c02c10710107005000c82d10400100703a9265000c1c15000580c2404a200e407803610f2021140110f009051582c0c00f241c032078595904 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 741508156 1250 741506906 741506923
    0x5061f090b0a180902040b09060d17131710060302011d04060503100212071d010516060515031603020904060209060d020703081602010b030c040f110d060528091d 71
    0x71284d43d40200c0c005608050062811b580c8040751403c406180250004503585980384014050003241381289584016460854001e80703034030140501225903030404041183c020301241c01041c041d010542c00756004601522003640c1d41612662101c20051070000185e4040300d540951080d15854001070544042c44002c1590581d41c0c00540d0751111000c2c4883d1211000d13218804110717100710410320b8404a400d03030550f8281c0920b0300581c0d8402503207804103a0f803d12040500790303500d808103002d40010703150501d0540c882d040d0156890040d880780680000040b511001c0e41285480d0300040001d50203034010106000d000306050b0400b101719956404a0b00543c0044021440f24420b1100d42d030340701c0c2105203480c40d0610080c411240300a0110f61030302540c00c24140519100d040c0c04541c0c889940000100003510030a59459000c00c0380002d020340414403030305008200d080b0030311007061200c4010110044103011540e004038a80b5901100511407401040010a060444c0000515050040b01e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 741509406 1250 741508156 741508199
    0xf0c050a111507050307020a1d07260f040c06050406120902030f0303040308010e010506031509070207120c1a030708072d0309050f0c010c0b060a0b030f010305061f090b0a 75
    0x1a00c46106e40705109040185801040403a908140100d0713072441c010301c949610040601c2c2045418000d000c4041402140d0f22142e001440c1c144100a00c0d040d20007541407040740a0f02d114603145a48400030303144c6200e9401440001036003010305440c0443c2d50380003244460306c050111a40080a4601903095400590301240001c10800c010400c10f5025648103001d003500303d68141c42c60802d55016480103a0209219014500301000607031014003e2280c40c0081070a040d00c52079049451800b82001c8020b4000c01041148101280c6001c01c0f8281c1078910030311894903030303030002d0700c88910943c3d540e00300d244140015284484030844140705480d0300410b040f1140c40c0440c1501c1c2610b4410305044440030380e14520f40c403010110b21940e034480b00780d00040d5045100746420303880310340206628030601e40008040400000a00040d140d0041040b41282d01a505941c1b5a4036251070154826059010309800601c4000f030a101e03441e5568000d4801040003061581d0a0780c0d41c08090f000500c000e6070b05d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 741510656 1250 741509406 741509413
    0xa0818070308032a07021003060509190f0516110109060204180c031109060912070e22031422290702060f0c0f1203070f0c050a11150705 60
    0x1c03c1300850f0f000100f50a010b080310b03048000e8601c03c51030180e0b0003103030000382c4128190a44050303164040d40c000b402410001d84203041034030341070200109204d415848002014603007542c1d89580301c0c040c0b1400e400748150116903840e445814204440c0000c0d80081c45489558074000b103000240140300600040030140f10107841c1076090740d5444100e80598800345d080c182440444003d400c81ca8085a80300c05048980f203803180d002c400030071a8440040e07240d1010388603010010606440a8100910810002c01c8112072072003070300c0840c001d443c958880100400c1d07a580052540d90f0b0148060709032509500d40507802c0c1c0724060340322007440900f03034850907601c10b40314240e05212403040085107654181e2900d07503280408650200d4011310956010a6003030030302040001600001707000081c0040080b0b411540a020340ea1501c1c4003980c81075502c207010813844100c0c02d9a55000b4804903140e540c1101c05031440305140c1d11072581003040b4141d0f06034026000e070051045040a07001510200c0d009a005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 741511906 1250 741510656 741510661
    0x130501030c06090b07150c110a060b0a081618020c0d0c02040e0d140708070c031406060915120c0a06031a01020303060a03150b060409150b0901050a081807030803 71
    0x20f000e00c0c00540003082c1500082014030049450910809200300c8400c0000170307414800302e000c46980c40307242e40200d5903019004003001801080e8011034251402250345108155175550352954030b040a1054928040038141c3c20088800b0036883e0328001000c2600c09442c001200240c2c60606900020040c040341c02c4a5011040d81094460444410350705002410040d59424000c2e0844103281e82a6510180000d0713100704224186060b1070601764011007038031201d5101c0c03a141800d02d07007020204026110f82400500c0d649410769012340203034660162032084003040300c00d10904601c0c0d0885109144a035020484841c0c4443e00c80d40e0042006603400034040751100752011040c0e0b030b134107200c4e81154014001c0c05120f0b520454060100c941c80a42400e000c0d80d00c598510150019204c000c0d8071003008070b03000810814540084050300c0c80f1842c4003000685900300180307280559885180052010f00200503c1405a0340b129045000445015462500906410320b02a43c41d00111030b001b402005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 741513156 1250 741511906 741511919
    0x181a12100b040209010c0215040e010f090b03070f170a0206042309040c051002190311061f120201090302040509010c09150206070e0105091807021e10020306130501030c 74
    0x41c0a09120115810f500d800d0a0100003862010480c1019201d6214412421200b01700003044400901c4000d12a211541c3e44901c501c510000d0761145000b66030502c030305a8690300e4041031140a6655141c0b441007060f0400e015180241c0701003040f00d40d544103c0120138090703560403025100616000c0207101e0000100d40900c2100c2402c2208070b40900d0055003800002140703040448103942e030584984500b4800c2c00d40032031a1020100c05952035081d8030341c0020500d80c2c01408007000c001b00c0320480f801ca40ba8210b181408001884960084d070038115000d103d0480b4a044000c1603c0c0145408144603440c0d80003d01250800c0d1440006a90740780c81c20598a0b0f08004a04c00030101503018120020f599007000e915540e00420000410450500014540e8040c1040c2d07489400060a059680c0405482c1d003000c03070350140c034403401501c500c1001300c1d40e031461441c0440000720f00c080901001d6841e0404a0081d410107000f146d80300e0f21304540d07644881000c0c07040030700a600981c0c0780c0d840700d840c102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 741514406 1250 741513156 741513161
    0xb120a0914100f1a19031704030c060810060509060c120702040b01050304050a020105131e08010e070f150e060304260c06150109051306140307181a1210 67
    0x112103880d0942802d000182400b0302e8040041c9502041d0381081070812080140300384034100b604010301f965109003d0200380d40c07414000d4815640f0400c4940c8a4070b807540c1c0300381d4003008101c50000e80705143d00400d202407440762014058000c00506483d05091610101da4240400003104a86100020565a0a52901e800355100c41b81003800e205107141800d8403600d0b02c960918001906120000520940c50501038865130b00500340e8204592045006a10010440e0000e1240142541c2485043c0d0b420180210701d8401300c0744440d00881e085407400410394a0000203014000034461001c2800c8460740f0f6030380045225511440014080c0103200c858542c20100c91000040c48540a00249841000c005821500002c41d262a07c41ca1520480121142c040343c0e0402500035810701116101c0c0c04035900030354180d07021289400300703400745031082c555030f000148901e410101c45103d15418181c481d07880f9000e41000c0a03a5190007440382e1021907402c02004c0c0014a05902c1602060018056803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 741515656 1250 741514406 741514421
    0xc0c04060515030708090c0d03030b03060a0c0903021201020c01060305071d010e06060c011d03040905091c080901110a050304031b0b01211a06030d02070b120a091410 73
    0x40b2104520589002100c582c6804002c114130b050150f00300120303802c0042040b003418485002080c245603582e40345002000341c00c020340b80501034442c0b000070606806a0b4003036035000d6415541c5a54044e4a1034080141c0056a1001d11070255420400a0004002070203494050760085000b0309946203401301d4440e8007a4072145404100229200600585440e0700505420910445a8940354608400b0b01030042c409c28aa042c0300341c517190a01d140301c10011018104442d50502c0401c42c80d51219072403620f40041c00ca106400b8040409650f0b00380d4002e44199801408500c0005013280c52503800c144035502c01aa402c0100304080100800c065202400e5048501c485032480103569160f920384880400c10b01a00c06506a40e01c015200d0506200c030032442982c020001130703411039091403011030325401511303024000d0050b40140002c2900005589044a40e20b0081b80d10b4410b02c16000780c50141c000c1c105c05800c07902c0704c1507000403405000511045005036000b421a41010700403031421500311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 741516906 1250 741515656 741515659
    0xf070f0608010608180124090c081303030c090b070b01030b090f070303030b0d0209010b03011415220504050a050a05011d0402040c0c14030405033706020f0c0c040605 73
    0x2488010b204040e4043e1100790130101c0780b45c07518940c0ca00074000c0342c0548040c1c04400c44544102851102036200102a0f0044503420542080140d001400407203100400300d44031a400c00f05003100c000040e210390b21600307600150b0f2070900c0009458071070b054015400a001614100c01e030200520620160302d9141c0e1308401e00380001c0501140b80566103840c0c0c0981e01c405028565242103000c1c4a0f01c541d80c24000480d0b004010740520741c1c4038260321980f030f0428096690400500b031440e08075400c05070052586a480c45507000e04198254810b04203206a89501c848040185d81e40060380751100d018140c000e500301c2d0740c081080e1401580c00d5088a01c141e121480074072400000c94046015a45c08680040d010365000c189800006400d4a40044901e001058040a80d80d4040740030404006001628812400e981020105010300582940c0103040e020303000c12071841320f14101000c03240c410a80351282d540982002d91007035108246070096210000c03140c12022101c0500c3c60241320b05400b4000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 741518156 1250 741516906 741516917
    0x20f131a0d05190c1511010b04020412080c01090803090c1906090603020f040b0408060411090c0f0c0109060509070815010b09010c0c120f031806021207060e0f070f06 73
    0x1d00d0380750035660740140c0c5408480c80441002202c10f002c0d0044000010788070711440c1e1085400540401003507880c082103812240e510340380030a03110b841c05000321411220088560b01044d041ca031600e28156120401c00740b040d40da6000080002801c1001852003101c00002510100ba05c4c48244a40509184140d45004560900c18401d2540044500c01600c1c02403900503151444415040642e00c101d030407950807036002060005640100040181c4150320804e401d4016241c00c405026071401d080e41c1032808100140440c066070200e040c060104444404000715041150340c0740c6408a0b841600c104c0e0300e9421000c000d1025900400034140031504043d2060120b40c5800b003403540718010107800c21304010300118020305110b0364581e04405040b400b40403200039a024a048207504000640072404140b40d8942c40066200c0000400210b415640203441403800303040030710324144d202d00c004a0b00580d0f14000c25003c2801007002030401031021008259950400c00c143c050f141066122408124 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 741519406 1250 741518156 741518179
    0x60909030e041b12020d0908030405011b0c0507211b050a08160303080405100e010209100e090402041d0a05030301030308060607321903111216020f131a 67
    0xd90100c40c0c07254104d9424001a200c0344501e0721038003c0e050212000c0e09641000c4140014810190300403c0c0512040c24040b09400d00403c09980100f404540a00f40340c010030300412180c000f440c0303010441050340c80c0c1d6041c24106a42e40c40c81840400310041c0b034068410501344501d007003001ca0100603103003460040110055500c1e10b0400042e06000040401a4410214081140421034034002c00e480d03982c10f106019401240a000b900003010044c490442c4005101600b8010050341180d80000340200c411a680e540034003002d05513008012070010400c51900d070341d01d1024068012014441c9015694079499414010850000030300003d02c5000104005000601c000300904030301c048044804c1c0741d0f0005081000c03c6d4078003d41200c15180103007450380a142c0b1025800800c406e210303031240c01551001d00c0b400c0d5920260300c03c00c0d40d08240100140c0100c56040f211082c4031910062010b1054801103021449c2c01303018000c0d0782d22803510b0314110b00e880651103135000b01c0da15090340d407000c841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 741520656 1250 741519406 741519461
    0x140a031508071a07060209030a08090f090c0a030c02032505060a06121103010b0402031617070905040f060f0608100e0601120504020a051f030e01020408030a050d060909030e04 77
    0x1180c40c3d1252120014000440780c041040c9901551000003004003035030409425410142203542c800d810851040c00340301c1d0f040c90541b030141040360003031146059a030309099024400b9002812802c0380401503110500c9800c50360450301c60b110310f58001041c1000388019407482c000303240c901c010b0b085401c0b49040a5052101020150307110115640061235081708980c0c40e80031070f00600c0c42c00055500103000104000c98410a00000c1e0700e40e401c190f07100c0c5034640e076004061522400c02c1d04e00c1c60016008820810075450322350020180800040ea00140c801c0e9110811341d64508998496004203c00c2410003801700303654540789000b1300c4407040f5034800f803604000081c4040418841c440d00160390380b020a0540d2100b00d04136014000280c0710742c00d07000440c20081907104030034500340000b0b405c2c50071008600d14180260340441d002c900080d41010743e00c910941d03543c0c11026480105c0c0396664000518145d0602880b00f11500946410604545010510058801c00e5200c854031101030031291241 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 741521906 1250 741520656 741520679
    0x20c071517100504090b060f030a120311130603060807080307020d08030c1b2a0d0201111f02040302040605011e030203100801090506100f03081207140a03150807 71
    0x22460241c2904035502c2c000040b800c004140c000f0358201d4a8000501c0402600c0344200e401400b003180c2c5401d2840c00c02003050741c0e0392008400145000c020010210703c240c080d170070150000344081e41030383c01c010500b50b625400901c55807200000a0b1107203030412103060144203070000f41c40700d940074515000b580c0d00400c500c0c2c0711081000f00444c0000001590902108003919034004451138032030350070003410799002d40d00c2504400750541c000f40302d150302c1c1c10882c1c9c9014000e0800005080c6904446050700103580c10704070340d016060180980116421000b2500744080f14182e450880142c40300d09500510040311260b400607418841481c007048003417003506401007001d1082c0d142c0036a41c0d68034081e241e40a40403503440310030f5560070245844100800811442c1c800c040d200c502e807501e1907440c03c041b0300d11255031001170003801040040c070101c3d0b01d04240042e44041c0341e0a02007d111402006921680d0040f03200e40006030b5139160700d0420140c451568030003410a02c0040002c5801d04114509 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 741523156 1250 741521906 741521927
    0x106020303130b0604020c030a1718070905150d06090b13030e040e07080a0602070b09030313080c0106150e011e140702190e010e010819112101020c0715 67
    0x10703900c4600004c0455650381c0455100c00301200580307854011101000d420a030040041d4000f008d0450002841070722080c00c5080c40304000c4004242180c039280c851402041d02070071581c6140c1441c461040c0300d80b07600282407903441c8201400503c070503107414050006440980926030307206003d2103c6010a50000c14068040022200011481014404513150450341d6100d010035029540f550400d01484d5406042c8a0740151103100d620350303c650103140c603448100d0381d1040c84840e5019680108030500090010b4090800000580546804240c0303050300d82a00b60800040a820b044c5d04903580c400c0540300040060309402d40075814046025010604a44003030112400201c0c00d28190340c1e91350003034005c0040802d20340381d0003038407428144100a02400b41d5120300340c3d424000500058001064403080c84a101007203220845690742c0d60b80d20081e01d494661048100401c040160042e0180d098140c046200040e900c0308800001424806507900c0b0b0381402da41d00086c130141ca60080721584 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 741524406 1250 741523156 741523163
    0x203131502070509010b090108060409080f07080f040e09010f09030219060906020f0405310902030c0306010b0d0e0109050c0d080d0c020a030e032b020114041a010602030313 76
    0x6111000c126001c03841d00340e50354401c40d0300c80d0403440001560300c8481c0007840106c0080e40c1c0c4104540d0346d1018031040d905818002440410100040031036800e03c000504950703031242d8482c9250084074110700301560040c0c1c00c018425580c0c082030109548091041c02032480094406128855843c2c9010307448010104c112440d121003c0d418908220055115820b0190b11075804c64451040f4800e214030307038100380240c03405041d10140000c074160a483c07400c0e4002075282c1b0002c400f00c015440c00e001824194034100d070584519000401180d409005043c041d1070710080310b40e181c00c2c440c0d00e01c0064803404070300c084445c3d2500c08080e021407408074411102480a440c4c501c1c0c00d01c59440d05907141c2c0710307085003d00d1140c41c0080c0012410390100340180814026600c014074030030250205620750361140600280450b000c10459480911007188800d268091b000020305c0f181c0583d425101c0141c202e0341200c40c03081c04080103022104401c03159002d4050361000303500310300d4101c1c0e030300401410090300903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 741525656 1250 741524406 741524429
    0x50a15050c0f370303020d020715051b04030b1f030b040303050403030b0612010314250e0a0c02210f0a081006030605090408030a11071406010506180603060402160b1006020313 77
    0x803a003047c80e82e0101d900c00da5220a1030180000c0882d0400c0081c00c0544208a400204c0d0200d0b400030030600058405032600001e01d085a07403248884065007000042e08454084500f000000108100d8118244580c0c000e4038045242e01c1d091030024111075101110500ca03042c18001244007440c02c0c468030b81940c2d17002d1900500070301d0950701c562601481005280038011000d2452190381c070b102c2034000450380c0c0c00b100800251a04206941a03d0a02c200700e00164090b45071100c84c2c011604000740b030640400c0e04903161404c140c0c200b0200c0c3c0e0020042e1400b060056060150850307c20b5502801040075140400030141440e00241c0d5500b009800034042810100224401c102030350b00590400c0808040c032952132000703140490400500745c1003d5254001d0b40000103103800c0c414101e03048001010031200e6056441001c000c165000a050039401a5080c05464811031004421401c50740c0206460840d84c07400d000400103004c0c1680050007150001d10030341e030b50b001007034044130146c80d241c0614 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 741526906 1250 741525656 741525667
    0x605010201020f040e060d080a2c09040f1b060216052b110a06260c0d0c0e04090321020f1204060b03011d011401050a15050c0f37030302 60
    0x100c59845087c8054012080011a07900c465080703141d61400100744401038a191802070500c80b00d210044654540024003030000400141f41ba40d4017800451142103c02e051883c6804182840280380c0c11440159000c030340d4803802421410411802014212000d10000c40340300781c040800340d51203501a186100c4903601d0020414680310000648001030482d4180c1951107000070108215940c41c0a91444c12400b10b03120302c01c82050261060050a4110b450400c00001c048000c3c00b4902ca850200440a24600c00380d64441c021041318902994540801151480c0c0005842403001d0382e080e5441c5c41080302c01480c2000e10143c030380d45042c1c00500e00607a030311410004090a42002c44941c1035180000d034221f1050b120101c481ca803084000200980e901c200e882c2000d0701c40030701541b90700c003c083c3c000f0019030a40b60042000b0400750b02d441400d101d00905814500000c0310200c980a8000c1d2440d1080017009d4001c20800041c09109807440d40d44030440c5165041c4003c4002d010141c00264 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 741528156 1250 741526906 741526909
    0xe1e030d0c050d02030a02040513050405060f060109090501030f03030c020f060610032301031205071119050a0b0a120c05070b040c0506040e0415050405030a0e030c060a120605010201020f040e06 85
    0x2035903d850714000f4159501e180ca480300d14000d60003401a00e126001b42c0c091150301c200e6a1155520a541c8400101440d0300e60854030b2520700780080603541000078000e000b29030070105008560007140710303c284034914201e9140c042c0a07100901c1c00c0c101194010b49070b4621580300006d040b0b4003c0c000740d40e50740042040c0707101180a094180c620b84107058050110400f060201d1008504032801065481060380040c030003210790340b10300440500000030103154200340380740c05075065084c11000a200d001c110f584d50049502c0c03500f40e600c01d00c4501c0b004120201e034544c001d04a02010322802404000403c9050b001420074040d0b40005450480a0301c001010811518100340c064074004200a45980c0d45a034420a5400101da0480700301482000c0086512918010303240515030280296040200072002102c4250081c00342d90340c1071003006030b544032949031031005024011746541e607004258500440003040c0da076142d00c09411684100502e8003000d081500307076405d88034000045005501e4040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 741529406 1250 741528156 741528167
    0x20a0f0305130816140f0405190908030703050a050403120221090a051011030417190905040e0a03020601060302090a0306060b090108010e1611030d0e010e1e030d0c 72
    0x1004401903101c000d030040f8024000298034404010400d005145003030716140d00920707445d9410450344c3c10100130f0341254454940b507000642d10109102c007250992980320101d006a1755010402d48461200105021510340d145c011180c0c400512102408942000e0750000d1032200c0b080c611440084c0d0224050006003501400300c91a2442800c004031706042503030115440b004c480d4021500c40c8100c00ca0312440301d0080c0500000d01000d061076900f0f503030f00c9440322001010100070002c607d420412181004d12903003d80499440c10302d644419105091105020481e0240c1d50040026031100b0806800254006031003410344603103181c05038035101d2100100d54404100c4d000200001d007004404118080203001400207401e0998811045903a03c20000c00301c55010349241039170611040a40b46011b00410075691441426411a460070021420314001c5038a007046031032469460329030361a0303c0c1c1400c00500995403403514820a1424036288180c2d40d03840381480c41c843c80d507141c0300742c00030460061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 741530656 1250 741529406 741529417
    0x201030207050307020a06020303240307060c020a0306140a060503010917210c1305010f0c0825060609110c0c09100b070606062a11061308100e0c01020a0f0305 70
    0x182138806d0302ca4944c203002c0d407a80c20448080344d10301c80300d11420400000302c041448002201601400300c0b40d051030800c07900802850401e0fa04040c54101c00400111a07201da84e409030040d244041c01d034100030280100b9115a80e03c690304c80da04186040c80410000c8140c0c20100c1d9a24854640ea0684c0c40609900c400401c512201103c01d41c100300000c5500600082110017102000322100544034801501c110f03003503140a0000079015140e00c8000380744000240718500a1500840c0b0032002c01c0d030355818010b0b20300c100300c44203601c0f030030100310071310150150580100c4008905400c0c03081d90400c0703036502c10340c46500c9442001c035800421a00740a0960034800740a260104c241d480150741410800b401852040e500056040511440c8041000c00d240220100001640b8845039140d00d588499010311075003590b106d4001c100701030550b80100d5004c001810024050030ac408560300b41d6008132144142008141e0300055043c0caa070780c0c2c0c00304140c000e40b40d101c403d01c80d000c151424215001e0289 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 741531906 1250 741530656 741530659
    0x150c04030c050f0f01080615070b1f06050d050a060504050903090915060f0d0f0504051b01020a0c0e071218031d03030a120f0501170c0301060e060d0f0803010b09011407020607020103020705030702 86
    0x22740b50b018000d80000d9648603d150819a03500c1e0600040b00d5121518180f1079040040c0741841101507808103a000f903a004104040c002c00d450b511903002030112441070703442e6401c41c1d00002d40c6c10310343c1c1001004182d10a001c0352001c4215504400030502910600032000e810810028543e426103003240c2c0010320b103100120f0104281c0c5001c2c42e10b00c2d5501d2020040410605015080365032561001950641c15548450038248841c501544002c001c20041c019a0078000c00808008070280188603540c1341484400c583d2002c20039030300b8041d06070a04201c40412400c5250400440c9403800000c4401e20f10301c5160408c0b01c125041403440051080c0c40da034058180c01d280001480c1d0005800c000c0800c595541692040c044070f808240c226015413040d00c50f8010320a00059152402003801c040c11401803140700c12260080c4d4411300181d009030020010003401150b84810303540e0000810384c1e1044110700251a0082c0c41d00010914050340200074109500000d04d5820030a01307006461450307030f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 741533156 1250 741531906 741531949
    0xc09090c110312061801051c0302010e25050f0612040302071a031603024b04090b0a06080a0216061a0108090d0c0212150c04030c050f0f010806 63
    0x2100740300103c48030019210240b064008110708400081441c0c0c50034100c400041c1001007006940e0052040701c000c0c05810f4065550f154040020050300384420360444240c420502900c0300e03010320b07021883c0c92582200d4003441c01c61121076881c1c2c40d91401c44041c4512a4001e0351195903c0c40c049250144a400c0781c0f088a2180361188507200c40e540c060741c007841803100344002502d00d28004408074090300b0003003124292801c9120441d4201d080c450700640d050f00d090741200c40e8821408440620f000d42035050f8060000604204004003442a03184110044a0318110030746800300040c400c80c00900203491b11540011191444c0f0010300b101f0001c0303070748860240039410003101044014810002120b011481c03031b1000907192480410a5041641c1603111401c48419580a00c042010154010201e80c0302d0348080c5120310340180210740c0b09d02540200746a98a0940c90f201305c11140f960f06c0030b805490f82820f181c0c6981d852031380f070700e80720602840c0c2130640e540c0b4100050341d01c07001540307a14203001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 741534406 1250 741533156 741533167
    0xe03120c04051302180411031513020c030d050108030313150204270b1215091005090d020c150a0813150f1a060702130605030106060806040f0c09090c1103 68
    0xb0a503005407031404085400c5c40c1c038500010040c0020380d01d521500700c0c1304410420000c4d6664043c15007401540384080c142c0e105401410140b4003c0303920080039426603500110b00c610131519a4012180034001c00c001850460802d44031562904140c0e120080a5a44076008880c0030041c0340d054a004000706960440c00b12103d4200c1c8142a0404624040031820800b0450142c10640e050904420801c2c4c010000c8a1091040d6a454213010b0850409070007078000700c031208046402400d006401c0381000d40308924030300c600030b4a4908000000c1e4028501c002080c1c100f200308409407a4a0741081c03d04141e0b5559907021820800400d40d802090003407001c044030b190144c1c0c0d6024100b0380c1d045880401c44840440050b0101c8a0000076550f81b00a003003002e0790040c28844444000c0c82c00080012420300e8560300041e0039540c40c4e400090014a9001c20031156207482d0150000e5005606001c1000c04240c0000612800680c015024216200d01400e00e10358810301101c1032003171403031060b281c440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 741535656 1250 741534406 741534439
    0x1b0d0803310b130305180f150306100c0201050304060504110409080406090b12010b130e010815070f090326030a05010f0503070f090906060305030a210e03120c0405 72
    0x1020341d00065404065040000e0075560030b4956a400260309030715540d040102403141003400980056000d5007140420f5100c900c103480380100000c0e05600400070039141c2c03601405121340c1240d01d80341c2c48200000c0d06c40b6200984d802504503900907800001c0402e065850341081d020314100401001d4100d880c1030759002c28070248001400981c0d42560340d0140003650790103401240d004440e079903600d500580f4010000b214110b0014200f44031045403c501d42c2d607440f01c81800304c01c1c09038071284854002c011107010316540c981e001c6501800c14180840307445d040b0700e0010b00844040c040107200d01200340c032030b18180c036100f819040040411281150350b45130000c0002d025242c288600f04039403941e16008181440e010070b0031010303180b1450154910302e18010300080070f484030b071009aa12650740c0c00003001160007480249592181ca454401903000031840c1d02c2e055101618140443c1480c103d240c0d84400c6000c0200c8440e0075084450410a455194400b07a00b031240381c0c40310758042c100800030084d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 741536906 1250 741535656 741535741
    0x1104030f0b0402040c0c031409011407080c060105011e0e0f030a140708060c1e0405100c0b0906070c0f02060c15071101050c0f1305130603051b0d0803 66
    0x80d0b4801e58090003061003500d0282d40711186404018023003a00d1039007941500045101030495100145005001100c00d060382417003aa0108105440c0c400c40010001d010a4040016034014402840c003400e400540c40303500030b48075007030440c03800c200a014507a00310a6903c005800c10318210080559904080510700700c410051403440c8440240200400041c25003004a0220302c83c0a210034036524150f81d581c0c908a140c01e908003d00303200030b810b010105041d1203010b12941201d40c00e441c1c0105003450b9050040d1030380401007144201d6840402040b0902e0340c400020f5540c1a88468150b9050f02980300051a9006607076102016104585a10042c080003048050041c1e0003600c4c1c049100c441c1005842c2a01d404958030b4a101404120500078002c000c00140f074100d145182624103503880f44c000a0350015921400da10071500d42c6c00c24024024184000503144030380244c0c00d00525081c4000c10580d003012040600504000710001e64410b05403000c001c8070041461420008402d1380491b84079 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 741538156 1250 741536906 741536911
    0x607032705030f030c0607080c1303061a03010b03100b060405090a060e07050405010206040b06040207060f0501080d05160305160c122d121416052e1104030f0b 70
    0x480c0c818404212140b58004c000c48502c0c0c40c25502911003542c50420075541510090402d00b2003403000c1007110071101ea2050510061840381c0c40110700610300308016400fa8280b4000648240d24203a002c00301030750001403003210f0660140001c5441c88208000a246025691042c3d40000100c2c041041800740c50740490700380c80e42c5243c0c03001c103604e03030400031901402680544c5015901140c0030401140510407900d0b0300920003030000d86003540c2541d428065602004c116900b0b540c4070001804450341c01c0c0700920b0340703203014a40241400c40400d00302c90203040c5410301809010b00050b6040e440b0b81500801c40c21786402210550700141da4800e10100b8001e20b03281510602402d4411010090110a030f01000076501c4000d22a41d46c055192105d0000244120400740700440310038105c1d81c58564007904102181080000141d141e504000b41410b0b1212143e10f00000310000c00d00c0e901200d0b003481d0300c000c0034101e070000b10441c4e10b141180680c4591341014ac40b0690542c0708108204050b20f0f82ca1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 741539406 1250 741538156 741538159
    0x180605040506010f0e0136050103020306090a050304090e0a080301080304091823010e01090803010f0b130308070f0b0112020f0402181e0604150e0f0f0607032705 71
    0xb102607070380303c400003000310b15401282131100e40d44004201d02d428004051048242d03c40203a02d9591143d11030b014544899031131000c0c804d0700da00c0100194a01404859440002d41021340401180c503a030b6640c0381c2c8a1402404070b201c2e904c83c81003030642810801c0744201035002000c42d80d40d50311520740c260b40340c2081c8219000281000341c5920700385400740c0e4a07c1d040750704c810020b10451484580c007074603460180184009660300e1030300902c400d209018541045006048095485d4182481544142c000350000700004104002041034a4090318649085a4111188584501e41484c144404a944040203451180e0100006c00c140350807819045196100321348944610440300c0c2888140e000c3c1c04140041e1941d104212031040c01c180300c0c08007810020080c03580642d01c25070f00041694001343c018011200c8103922014080d9002200604400c1e012102e00e6501c5140d0130002d60602c1d40100307000d002d802d010417817100300742c052603910360002640e2100c045191b1a582010b8044009803040a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 741540656 1250 741539406 741539413
    0x11e0e040f330b01080109020307030906050c0c06060307080a0308100b0f0301080c0306150f03010209040203090604020a120c060f120903020102090a0b0310170304030f0803061002030a080f0a1806050405 89
    0x118184142c03403052007500d450603100c9a030f5503841c00a00307100a4000411940c00e15403203030051000600c00340b20300ca104810b09201e2513110f00c6502e400750710300030004100d640030394403416041c0841d03000050140e01a5526183c1100d103691014120f0040c0503031580040442c2ca008162000140e9980f009503040c1c1d41d059045840c014603aa0426a4428060324020580084480f503610b541c03c05409010f5070980240025141c0b10018004c10f04076030007100c60883c0d0307130410410300c011454404554030092401400740caa90b601c49480b080c260384558803e070b0041c008125003016600f801007010304080402c640e0100300514660a01902035480102c000d0b100340c3c810000841d1555140041c0c0303024080c40b01102a005c0d041002514051440c40c40755180c40c8002d000000c001020f813010310079030a1141d80e009031070741080818095044514118801590410720420207441c0d8001c0105501180c0c4e841040a651036a0714800020320110758808251800c2e0380e8010140441034001034040c42c8528102d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 741541906 1250 741540656 741540743
    0xa0f1a040609171920030301031a090f03030606160f0f0308010f0b16022b12080105031f0e0f0304080706141804060906080d0305011e0e040f 62
    0xf942014481d26509501c560208086924050300c1415410300070f584d401c0c1c82c10132416503005060300e10b4100340e01c100c600e8911004150090052001c0745600302c54100f0082144440b03030b0051a4603400002d00d940e0082c100421411b50313601004003c9034405400c034001851140c5a820f28101d0450b074444241c01040707142c4000140002105c01c180d0460f00c07100e681070309080101c0c00c541d10201c89030b04166030125848200180c165000303040b030703240d48802048130a0700341031138a8008500c05100415105000d0b00348010000780e1000b00b05180d0208e0085810900d1301a544901c030024264000d00c444e042c0329520101100400000c024015180c0d02c90888095039651070b4222000b003c075460030701032003105100124005a103201c40703e1100d07400510200305030b5220740c0c000d4101c608980c4804003a500910444491940610074140909840f52040005d200000158031001d0b03591700c03e0141880c0d40200081c14400f04005001003c0d900c07101c40c02c016000c407001021403022100701106070f034401400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 741543156 1250 741541906 741541943
    0x12180906061d0f1012020f04081e07050d3528090302060d0608030d0f0b09010b09100512070807080f01081c0c06110307030605010504080a0f1a040609 66
    0x81001d00120010003601c0313100c11248089511040c0d607641c0c0e40c0380d01d400b844130120343c1e0825030140c40030345400e80042111401039040c1242c0c50f400c0c00c034002c0c1c8641010b541880380e030329960324904400342c2101c10101056441c01601c03250b5001500780041d80070780209003007030031110480203044a080114000f01c140101c0c0101ca28007410707840355040480c00d00102040141084130161240e4003a4039800034031641c3d0f5012050075030307002e1104210b0056a500d000291000d041c40748500303001c4203071800700c419030500845c1d441500c0307214121031040b07070204e484c0c00b5501d1045046840462070048803401c1c5081440020300006426240c1d90049142c49001990b14070080c0081c60407141d841d070080c03d141d403099001034240e10049101500700404200c1c8903004c101103010b030038a001d660241a03030b40c03071429220050031180640c003d18100041000104038160b00000e501043e90b402100c41610780d401480c207400e00080a2070f0b90004884404c6c1004140200c0d0303441404d0340340c015030010001e12500c0b007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 741544406 1250 741543156 741543169
    0x1605070b162a061508061e0f0603060703110d11090f0303030c07060f0e0f0f010507020a0309030b0c1218011109090a1a0d0506060f01020a12180906061d 67
    0x121501406044020560007040f01c0740c00c296090f0b040000342e1091542c0b109449818842d045850050001c19038513540c0340000904e460741e030720051910000706507083c08030009880b258040d04503400c040c2c8900e55280300c0001001107900910355002c04026902424103039520f580c00504195201c1ea400f1800c00c3c1c0d10b0704002c0200d0380b0510442241500d4404144c0c2c883e00140f00a0b000f000015569038560341010404001c40c3d00b0030720618005080210f045d54105095030300c014403807411904205007020001c1d4214044e0400d0f01e0340311500010b240e66000d41100c26024040c1148921204081844010b0082016015031414107200900c0b003c035601d00c501a0500ca416550f5410a92140002e110300600354000302c0c40c5a5194000200c8400b4003001401c090041c8005440c42d0300b2160500520b03141468508030b04031000c1c0080c04441c0296100c8181d5004240102d00074407481c176140e07010500070381c2003102c06083e180e90100040c607220100103142080185d01980c2c02000d04a515115240c000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 741545656 1250 741544406 741544457
    0x120a0c050901141804050109560301060b0c0714010e04020c011e0f0b090601080c1309060e150a0e0a1a03100507020d080f1605070b16 59
    0x6031a1262041c1503d84410260b41c000c22042c1d083c00d01d44411000290303943c2c0101030081c5088100821100b95000c0c040035490b40034003e21510038842581c0c210349940d02c4020104032100d94100c680e01070010200441d045070140044c0d9459441d1042c0820304d081c2441c00340c010100b03c0d00c01c03621002c0d210080030709221103559640d400300701060384840c89841d10750024a04420a0000490041d25404040116030b01e51100002c82a0701c600400b40e00c881184601000000c040340c41420f14200180007910905c0094400404c8140c0012121084420031204100405891b5000c011682d69841d16001d220001d40b01030b01c00b14540c48043d50f09280c9600c58006856802d1203082c074644520a480004000b940360500c10780040b200c0401c0d40d0b0780e060041c101a4050b8046c0403403c0c1c60550700003820702c01111501001d0007802c400b4080c0314043c8601284d48580301050030f00031150f6210003a43e19000c0e07410000c03c80da418900304083c641c0045041c49540c191a29142c0215020091102c814000c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 741546762 1106 741545656 741545659
    0x60b281d131109040b0115031109012303040305031504020712050a03140c0405090f090303061005040302191404062d030507030b0f0f061e1203120a0c0509 68
    0x50490300809142282341c01c101c144102200b00620b4002c2d18200c1d03042141c414a0711548e0007500c1100112204600a9181c4a10b01450020711070341c0102c44c1455006038a00080a480c01c1900980c3c550b6075014034408003000d040001140d5542014044804040c0c480b1f0885200707440c40610f9a000790084c01c41241d4980c20081031190110002d040c010790440c860703041103414000403095a070000301c1100c0b1000141c0d045013040b1414027403034101039840440070103004c03005411440e81104841504075006802d04401e4100012039003248903010110303034400c8140c0d10000201156107000c0c0c608140015903552640c8880d840e00b0000e0300110f6142100b00c003400000c0180d0380440d0380c8246da0301014a02440c03d0004911a0980420040e5a480c0845004545656681d500c88465000c2e4800c403500d41f5002c4060084070030084d01c1006245142104c044504c6100d0720032a00341403030 = true := by decide +kernel

theorem cover : BRFrame.Cov 741366906 741546762 := by
  have h0 := BRFrame.cov_init 741366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 741366906 ≤ n) (h2 : n < 741546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
