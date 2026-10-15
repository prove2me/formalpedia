-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4808
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:47:44.265722+00:00
-- url     : https://prove2.me/submissions/0a5bd2f7-4117-466c-9c0a-8a696078731c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 864568345 ≤ n < 864748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 864569595 1250 864568345 864568351
    0x120f0818060d0e010506060304050a2a03050f0c0402040b030f071b080a03060f0807030308090a02030d050316022a0307030219050f04060803070b1f03030908060a0c20030409090b 78
    0x3d50352a01d4000784135482c0a5064038040d42d080b10003044080c3e0039544010082e40d00d005040c61501c03911807980145040000350300040c52040010700310a0303108440c6a1301d4072141c00805840740340140014408000781c0c9003503d5100700000c15050181d2900c007815190789014912010001c2c2c00000c0c0c880038000e00300020803001046603010400b00d03a43c0ca400300c22a503461302505a55030003c1c102080441d1003081250380080c281819a401140283c0c006403138001402081000709a01004103c40e030284c001601660040c0d030b0001c1d0085222414920f10410701c550141e030b1070035069002204180d2020410035000e1503015052444c640140c0c0e0b000b100055061107694891240c5202d49020350a0a002c1e075030403158140011400d01119a840c00e0144c40010003400d6a0200c40b080e40e6100006954500d000314003035290421920305050881c0d042c1000103000710510340c1000c48500b641d9900884204090f075403071140355080c117040c41c0c6141c11071141da80180700440c01c000e80308007848400350010340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 864570845 1250 864569595 864569621
    0x1211070b12060a03020a0605090f030303010603060612021305152218110912120316030b030f06041202010204080616020c010804030c061a0603160801120f0818060d 72
    0xa41d1410104489600b050100a406c045080b10402c0103a008101500e442c000003011901c09001480c040717480c0d074101341c5c0400c2c00251a2081008604d8000c0b070194408419540294034150f180001c207001a5544d01c0340c240501103942050164401010580b43c0f0344200001c0702c0303060141507440d005586164000e0b07203888441c0141c0340800142c1742c41104440117803100344505209003c010041e21a84160342405c540c011014414031031004d46005520801c29402d01c69608803500320000e084802c2d0f440d2650003035001103070740d035040301d00000c44035880756000480703082030750b040c440480c068040c40c0e110062901c52081800780342038000740c160405001c84e90844110700545001110689001c3e100540401c1032020f07868040380300c580040d0103c105001100b04641c12050100f03119503c2214844150800900c07035490301548000f0b11030041051091f60180d07094243c89124504103400c1d4000c001c4040054124091210f5031581102000020091741c0c440c01c1605e40c440240c61440c00c414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 864572095 1250 864570845 864570877
    0x618290d050601081617060a03080a08012105031602030708070f05090a021611180a021c1a1c0503040305100c050f0412060b150a03050c070f1211070b 66
    0xc0201440d4200304811489603500c1c1b01c0c5038190b1721004410400040d100caa0840d43c64038020000c03074482001417003403503a107944441c05903243c8102d04001868230209041c5080c060004034011640c004255010303401d81070099260308400d440001d2600200d0390101d48540118032002070b485160140c1102107032002c0e00c03a0122541d52603040740803803150002080b9030f00d5007070074848017150080075044112600a80001c03002d040c80c00030b1040501048903404017090300041c089048001d506003c0300d001d043c100d402d020440c0b103880810b80fa110041400c902a0f01d0140d02d021501d4003048025009079000000d0f0b80d911038890030201d0300e0b00d440d100c0800380c50303041460482c0118803070340460780b03a42910000b65080c0707420603481000304502c0705c1003070300d98649a0140a0090b95840314021201641000c1c03141c0c0c51200410107000c1d180000c0c14139064540922044010030f20700c80380b4021103907000c3c40b4407042c0d001a041c10f40c0c0304401404024120303c101100401e203103400000600011158410030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 864573345 1250 864572095 864572101
    0x10050411031b03070201020c01110304110108040c21020909060403090f060804030827010e0d1d0609120a08040512030a170c07060e0c0405010618290d05060108 70
    0xd4801a141003410320b52200410b102c0d0207410001d0340d00400e0342c1c8009071800600d00d6149080d07450403100c4501040000040c0401c20032100c03414001c640082c04c04900b64500742e120032a0300325040c46503410311654281c0500010101e000c8205000b42d005040141a05100ca00c0d280e42e1402141c040700070811458020460b00807245a0004495965841100c82c0e0b6403641e003100d80000150402600702d40c480b41d0b4140f08107842003240c242c1c203400c0c0000034070001940305640c80c101019100b1818000451226075880b9448403641c4d5180d1010344903569031b0311052022a2200c1004d464241040c0541b240500c108500d0000400880d1801c036511056407840c81100c80c1c0b80d200741410741c070101d8907060640c90004020300210307500000e60780d02c1500b40755050301c03414180c80e21480c0e40714841c4c0044103e00480d103001d100340d40c0034020034600154804900c52003020b000780c482c041c0826004008406004404c400d02010702c206070305841e000c4c3c44101e50b400e8080075110944000d40816800000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 864574595 1250 864573345 864573371
    0x7030605060a0e04021005090d0f03091401090b180613030b010504060b0a030506210105010e1503030a120204090e030901030b150714030403020603090f01050108030f121509100504 79
    0x1946054603184032a003d0300e500c950342000001d560340410017060100522082010b07684203802c0c0710445004401440c110480c51600030002c280740e40000d0384980c26070113000c1583e6805100c3d903095030480b444e0030381c0e58000140c42c0303e819051003074040c0c0c4c001400104041c0c088005108042101d1180304220096600d032403c1100761038003401200d0300440148120312140b4071a4101c00d40064002e0070060805503894100082000008000382d183d0707440d0401080303201c0c8446211540308003000c1e20702c0807001462000036202c3c80780c2149041000101807101040740041d44c101c03001803841440c10000c075400300d003200e5141e400c101c4015010074a0100384d265a400c0440e141d0340c0305000e0000d440c0c680035169030f6002405400840c1e80980e4841440080010303100c14000310300400c000c0d0021329400814001017429150160400415034000f80000480748002409581c070030145420a0102c5540d8410509100441d500415611114450078804d015205046c02401d4a03016101800400c0e40c00c06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 864575845 1250 864574595 864574609
    0x11e09090803060103201809061207060f030b0604030c051804020f13140c2206050a0f0c021e0301060b070b06060717041e1203090501031a0405090703060506 69
    0xd04500d41c02c00024002c0c1d03100c0d500c00030240b011240c1c164005020202c001e06550002c07810340c50200703118440d0300c2603441c00d175012a900c0b03401101c44071032585000c1980b0b502e03000103204910900c0140a01301e06098000e41100800401c0945801e40303c5030350741084e0507000030510a40c2c0c0074a01c0303208206020905200c04a1103590003425100c4090024002d01619441c918003003845035548001000040c0c2120014500503880340300c43d1511140e03880d070300344005580e101d0011a40721100c1e10401810ba0010107580d28100a41001703a908401ca079400e0300c2c48e070404500207500003d082c640c0410041c000814502c59501500200300b80e41d102c1d000e910144c416148040c2440c00002c5c0065903510f048401006038a203c0d10080301941030b01d29090035544c0003508042d601403403406481400d40025411800200600d2400914900064601a1450206010f0300e8100b60f11030715550000c04074640d41d0118104050300c10401131034584089503c9800c42e0004640c4103050002050300c0d458036823 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 864577095 1250 864575845 864575861
    0x170a051906110306151c14010f0605031608060117100f1413180c030804051f1d0102120706050a15061b0c05100309021201360803011e09 60
    0x1400c40b00b890914102200f21036046081c0c92018085220b41d61121b0b44040c1c01400d90b18180f030094018030f5410000c05001c0240181c1000003003010a00030030508520580e5000d07001038550403c801c050300d8540040325200e4030409070400d01c0c407034802030110a091045400007240d020b07101c100b003d651109849215900d050500c680d001c050049030340e4a201550b80003110300d00d0103410303540e2006042c0d0b641a96001890f030040c0e900c070b400480d04001c60704010740b800b01549000701c2d09601003801c4100c090202c040c07210840c001854502e2545295034000c10400700715040e007110b22502c1e5140c501c3d2510150104440210303c05061040b5844110921280f43d001e503401c0343c0b80c41c0507108000d0b0300807031840c103840382c141e5845d4503103c8002580e8031200320f1020380d129503580c0462002a28014007082040060144d1810303891701d10300d48100c4081c80c015803401c02c000702d0480203445440d182c20284400d948000303060400000000200e940c07c20240c411450030300415841181e0f0f80340c244c034003151212 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 864578345 1250 864577095 864577099
    0x60c02041d0c01050c250e0604052421010b0406080c03062e120b06010c050c1e030d02010e0706020109170912010911120f0304170a051906110306 64
    0x407000e00b408540c00341c0c010b0b180c00440c0c1001c071034000030f000c80752401c030003400c1150240400d00724409101e40800400460350000b001e0350140114240485116502e415070064081c41c215000a0001181d56a00070380300b0303013410403e4400c480509603400900a044d8140700314030403442e0000000d10782c0000b04019241c104001c0c09040c0c107684034485030540000340c1c07280340c18500d250701d000340d4081e44800d8100d019100c1100b803400481003030304d48400001d1014290034140152402d01d0400a03100007009182c01105403400040d10b0b844203e4803000722002000641c0c540a04904031030100d9055020f03840740c081c032004980195a031a00140d080310385036400507000150300f46040c01101f0a0000a02d0004005000380145003610006030f800c456003c0c0c030031980300b00181d0f4050440e142c1065440f1681040340f0207070800c1c290fa020180d54910591203404400540c7d001768800040d014001010682d400006a5442003100d64240c050003002c0d401c01c80c2c40f6072a0060700c030114410502500d1140c480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 864579595 1250 864578345 864578353
    0xb010314040224040609060306090b210712080a0f0c080a03050711010906140106030b061e0c0f0607080c030f040f1b0626221704060c02041d 62
    0x4a40074030543c90301058000328108107a8034101d8201d882140144010041690b8581c0a10704200e0010252505070344140b00d183d0410b000c903192580caa40394103514184901c40c1e4030641401c1c3c240310341005035660003030020f800045145000d10020b000244410483d6070303280d0001c4003151009842c1d40f104030f40082d01e204028058031100d6400382e404181c21080d541008814040702d01b41c0142561030889049800c1902d48406140b0070300111405805001a810248039140c2080c4c04078127280600300504008090181100100c408001c003103e8000d0700326010b845022980564555840c0f006840e42c00004210708009020b84101e44166805148142018084c0d43c807107071200468040d450328151403000c0c04080b139103020301041d03040c03200801040c0c613020703420a2007201c01c1c20044140382820f0807107034400d001c00440d8102460642410100328114000c40c0e0400c1c24812200d104900068000d00000180030503a41d41203070201382c0c502d20884090007d07900c0c1001032440410700040180d50307548 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 864580845 1250 864579595 864579601
    0x17070f030b04060b100c1106030c0717070f030804200604290c0c0909070f06080915040812060f01230d0c0509030708060106050906070203030c1b040b010314 69
    0x519101041d00180240030104040d49200c0004041250030200d05d000720302800d03648010008104140d520454003200d45e503040d80f83c80c4a580c40c407841072400040249244034442501803462401380d0301060341144c5a0035001c2038914024085080c155019901044801300740032984120b1807540e030140b140544003c0c140b13850182100580c1c840161a040d02d10080800100a01c0c032030030140892422400c024101410080c1c1440030f424030240c0800c15640058405011006151040208481052a26420659903921311f02e04000c1d10410980500400c0b1080c0005d05c014100500100103d5070300f00456a00c03204100400301c7c103503180840c0400d4111a04010021040c500440404805115245001c2c01031142d0011074641019031000304801180c0700e203131400d080103024003402404006048650510300064868050205a14402c140005180c011502e0600a480780008142c0c12144011045002e90541c40a0320800c40c1c0910300c0c1c0644428036603c40e0190103400c5032802250300341c44d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 864582095 1250 864580845 864580853
    0x30e07090b0d02041e0f060609120b06150d0501031a0601020120030a0b0303070503460909050708180a02061b070308030f0a0b0108010305031c0f110417070f03 70
    0x583d04400e5550100ca40321140841c440e2402080461b5140400000e500c60400c400a4142100381d00526094012400303100e001880302903d19411010072140d065141c401124500550302c1295a10210141040000000c1019000c6d0b40318591800d90511101e5540b420012801c90301d0003140b11203102022004030b03108003c000c0c0159002a09600e01160b201d40450100c0d00d15481201c04550580c000a00c5c0151020201203030012030402d0302c01401e107992401c11060b250311074003000705400144e54196840701409019144010040c40a003402036140200003c1c000d54402c640e244030b15241c0746a64220b2a40100d668118a0380c02001642070a5102e06043c0d80c40311074407042c5640f8411401c000c0041201c0e0005103100d003124012014191070102200c00c15201c400050354144081c9000500c0010300110542d0400480b05044200e4101040102030103848603500300c184980c50500b003e184d80503110018829110100e140000742e45400f204690388003554812548100780841c4244002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 864583345 1250 864582095 864582101
    0xb0c011b050309030a110705030106141c050d0815041803080606040b1b0708060c03070908161e030605070207051e0d030c0302030d050a020316090b19110706030e07090b0d0204 77
    0x30451b548110b907601d5880d2000b19007168916007045c24a1034540782c42202c070b40b03042c1e04101250b0039407050307080030740369640d03611540d60320811b050109014004002442c90740f01e20070a0b201140780107205125000049400402341c5100460a0f40050041400503480e800c043c4107c40403a024004014136001b4601841a60038110681121aa0086a0700029811000c101c0c060207180316540e05507803400c0428018120342c000341d0158020340c00180e6200552842030030640126200000c1d54100c81c00c00c540e0002144103242c1004151614203000d1040c19940013aa0b0420b407001503803c810000340c6c0c640003061031540080c2140e80302420a140100207840742c40c80d629503030700c01d00440c4e013043c69525500069410446030340038850381c084204010701034034082d0641c403601c0c01e0505182160902d101050300744551b260a0318001c240311100048a403154240701c0700e030349030007080d665a140c5481c00200034101c0042c080c0d4080c1b107569408039000a45104070305188100400c0262401003e900388409 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 864584595 1250 864583345 864583367
    0x50a1103010524130510020706020a0b0a0e100b180417161e030e0d030f08100512030a0e0a08060a090809061603030f090803060402130b0c011b050309030a 68
    0x1c20401d8200c44036800c8008094620b50041180a1000c103090106000c1d600308a001c1030011075009207420007292b9000725081c0400c0381c018028508607507480c0c42c00350141246422540c02c5100700074407124030b030b21a0781c4141f44410046568460144201d896920064416100a045402e0314003510380d080006000605660360b042c00c480d2141e946589820207080c108a00e404206014001128100360b0300c00107084481c83d0445da009243c00040e24010201d03c142c00504080c440c9610109440501c404680c100400d401000202c132a8902c0c0465516174001c2070052001c501c6031b0450a60303d20717240307001c04144c5800320014015aa65103160f02e01419841c2001c1c1e503614000c212207c50f0303450310030041c0110340441c00c00c0c4c1d4203507000d8a4000d08954004149001151610b40d1a1001665640403031b60804021600561980f01003c01c1c0b103400c61207940810049100025000d20181c4107400c03886c86101c0e40d900e0042c9181d20b004c010346461204645a00309078004002d01d9200c5401082c003148 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 864585845 1250 864584595 864584629
    0x909181a07020a08040e0402030606040614130b040e100b0603061008072616030506031b0f280501050703080a0c02010e030408070311040e0d0f0c02150301030204050a11030105 77
    0x4000190354650101d198040d0b0022907903146d40f441044254201045815080300c01503504020301e44c5820341d2032141c1000100050301c542c200203502203040714650880b1850700b00040c420040400d02c0981c05e41d89002c0d07040f0441c8024104007000301c1303910741841501d00c241000340500c00d02d03410041c403c07102e04000811003420f02515151803072110704030449000402a00e00700008407030038040d078407441d03075041d80009104060074002040403545000c520b1403000320380d240c41d01e404006040c00007180c800b09210215040b0020034220341c01195590740c803111181d9541845400640c84500460f580c0c49000009404a015440424204052a8060080031b902c1d0f10000071080034142d5160308641c8503900c148503603440101d0038424018007900541c090135086408000d40f51200c0c1c100d23900d944d04580d00c4000d002c0c0d204c00005d6050f02502e80c01e111030350700070f00e2104004241034000c45c0c1c9410a000a902a500d03100c0016900105803040e003506500180c890b6007141e20304400c002c081d46419452030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 864587095 1250 864585845 864585853
    0x414041104053a03021009120507030c050115060f020a0203070506030c0d0e01020a020c040e0c1011030403061505220c020f030c010203010504180b010605030c07080a0909181a0702 79
    0x291148640b19407412040a1043c43c264441c03c40c2802841c2610803044000b50910388038528001038035a6094110b4000e039420584d8803035101e828103075a00d14210b0000740c030a500700350482082500707401d403030415100303162a00b03610a4003041003280c0d1091100c2000707400d5440031f281070102e85880405164844e040c0340c0e131070b442c01d03043c85130340704c191044618a00340e160740102e03144a0a41e014050b02c40502d40948017040302922083c026580c0d511907040c040e002c4c02107026080c00d83c40c4074940c0e140410310a4000c403540c0d03650328070f0034000804006040310701e400716541000c6100d00e400b090104543e21207800e8186c006006030b00c100001d01c440844070b001e520403109c00b5087d11009001425080c440040010386961404041c00199104204283d000c030800c00d045d80001001f0642d0707075040da0018980261030b40c0c4c0701c0b032a0f90610b20690202801c090004605100044d501018600c2910412031081c4621034030392815800c0503001205c0203021003d000820f450400480b002140d105100c0d01c111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 864588345 1250 864587095 864587149
    0xd0501170d0923060f0c0705090105030118110303040807031a0c030f3c01081b0d0807020a18050a060b090a091a040504080703020105070203030601170402010210050c041404110405 79
    0x92400354441e40700c6e03510580040340100715901d014401e03e40180001da00034004403d5880303140f5540e00103041c009208500000c0b4907160382e2404c20548000d0840702045030811174490500c94020390003800260203241c04040090070301c0d550a01507a0141410810044c480c5c2c42d00c505e40040d4606024420120300603820f01c0c160003a2042004580401c5401007118055041c40c20103401c2909050f030121315080c0101c1001602d4652040c070301d01154000850130345a07402c5100252842a0651201740c05600400c01c007114003101da401703d80030b210007102c2000081e46e6680310124500420128944c405070b080010000e560030b03600900c010640641030903400402140001d021288159415075400c0740100354503041540900c43d240d0402e589000650441c90300c14002401c1070b100446441c20744090001060459008002c000114a20b42c0010700540c0f80c420410040760b0840c3c415085a112441c0e007007480d0f401c140c403645010800b032606452900e400c0400348058500008a480602e051140c44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 864589595 1250 864588345 864588367
    0xd0c03090b0a272607051e220e01052a0c030f0c12070c121103060c0d061a070632060108280b04020d0501170d092306 52
    0x10408111480f030f00446151400c2c40c03c802d07104a040111040c3d1000701112a030b0215030002804000c03120112219032143e080b01c030000072034407100e81d80c0c560410000a0000d4261700c801200e89100905100c041140280070b49556098600c01c1c0d0b14a03205d100400044040d401700c0c002400140308001100e00d02d00445103480d0740c03959001c1e803400c02d14001c010920b2161420140110001590351024160408a8985404035141c40f941f24040f07101810580c41030410900503040e540881c0b008081d07941e540380004111801c1c0d40805070410304189001400b0807902501d1b00c049044c500301a20640c00c1240b1581d07504014025100509890540e564403151008906a1240092940b4500019582c00c0080c005030040c1d10140c103860b11007003c0000c20b0741c1001d490104c8a0700040c5c1080c0031070700240b02c03808100284942c00e050300c404c81c00c0c000049444426805010a8920040c0441d018040006004c0b1000f4801780920364617035160122083c6424824030340100360352070042200b0f00d03111200302 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 864590845 1250 864589595 864589637
    0x616020a0312080f0c03060d0f050318030c01030221070c050f100c0f02100f1e0504020913120f05042c071103071b0504020304030804050d0c03090b0a 66
    0x200440720440b0858016600700d6000c0865900450301e00700a52450619550080d40390000910f10b50103690701880342070520440d80c823007522094001040d00d98402200720310a40c40c071a6410201e0007842a0001400d06522034801c40d024824040190310700d6a0a03490003c1b03080c0000b410070020000351030b1005012440038014552007510030b5000701748172107403c812203050301d1001c04500180301c40e00300c18881325034021034042a107100c0c03032100040740c540784010070008104108100040e84a80a01804a58800d0740302c5030056000b1240b0118070b80c0c413418002023002c10f40700010101e00440098850f52801350351400300440300781c14064102621501e004d00220340c240640380042c44a100c4080c003208541203803a8000d403482c641a206046000308250b6644a1050300400300c0500c010600d0503425408030807005040300500a66680c00d20f414000e00710705040d2802d48907801402c2001492600904650302002c0e890b80352296654079015001d64a50442800b1400344440f0400118000713184030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 864592095 1250 864590845 864590849
    0x40f020d1113090c0f0315090203090a0512070807080f090d06141b1c0b0d03020a020a0b1305014a03030f0d021c050a02031b1303020616020a 62
    0x6081d854690001010800c844507040d80220301e40340c80c10540c4008a0f034424001c1c08085c0c0903040c0032941c0f8040111912203141503901c8201d90a00c080240903100b1804600c1c82c02c1280100c08480f116084400c40a0341480392010042220b54100701c0d010005044002804180c03068000710707801c00314010042a881c9461754811110fa5903248000c90401f107030b10204136085200300143d10f0035a541f80d0101c4072075101b54015402c00066082c0e00c900c84811796000341c41d8200c1c1c00f40c080d248201c0c003440c019550b000d46104c01c9100d00761114010420392025025501044c203e03c0107101d00c0d51a0000640b05118505442c4c1a003c1c0c042e10080285141c1c41c07910fa10b00500c0c1c3c0c20301c04092080b6100d03480b80030700c41c3c52000e211f80c1040010405c480401410b845401c8280b100041e55a040340d41300b40610140092850040ca00704801c00c00c001c807141d4042c40c030450580c0244c1182c1d00d09801d0310a000e116014145c0261424000c080c809800c001c1e010b030070500e402c0020305214040c80e80000f0703210201c903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 864593345 1250 864592095 864592121
    0x102120a0306050907110a030806040e07170d14040509070c02120c0f10080a1d100b0a121203051009090804090b06030402090f040309030c090b010f05040f0302040f020d 74
    0x140b2010030140c00c2040015a00103010301d0600c0c25980c03014010350321881400005010441203102168850b034482d84501c1c0401040c804039002c10f582c0d820300314080c4404c0c1149808500aa500c03a9039864041c00c2c00c6c16150904d803140b1031a2505180c208410703984080c0c00380b02040604543c400c0140c444010a5071200c2910000b8000388100301d040142001800080a0003040303c082c900040940103030016402841d920703004070b1510224805150f040103002540000d80c4603101d041010384000d40c2c080d10340102c082d140a11078645801d204480b50190520081401170200058085a4442d5002030340124503070a02c0c00311580d503006190b064cc1c083c800e069840d00e10010b820001090503120340c51842100b80e80302c80c00c502d040d80000e03192103001480840e441101c02e002508041c03003084048080c40c0d0150481c00e02c40d45951410004004402070180400d2102d540301c000d00b405142030f18110359504804900c010b08650903c0040d1201c01143c01c0d20540034000007244400a000d00000e0401d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 864594595 1250 864593345 864593351
    0x50a210207061a0f0a09050a090206130608090a0c0b0c010b032e0908041502101a1014030601050904181101081f030209190603030503062e0e0102120a03 67
    0x1900c41d0050f40f0601140580726a0720481d036000c864944210717074403c681d0800400220f03996205980b40240554203c02580301c48005039080307285101090f0001550700540d160700c0107a4860030181da4032601c003038002d4841038101c10104a41c591110081144081c58800454908900380120b4508000032419980d0403010040c10541001c2e8035443c41c1c6d0160002c14240052081e07074448414920840c000d101010040790030f6580018020003454103910203000c0200b0152501080c003603103010900d503041e03100f00058401805c0b03403403080c122144500414580b29145844800055a0b2a84032014840d0020f49034000380e40300c480ca074401341516078000c620680c2c4164480000520301d203001400104000e152400fa070070408031a0f115807040c1c0390306071101101d070785441c500c80d0014002e11004e8038038141062000301c00c03d54000095800b030300b0190b68810f800c004401c507500605c1c2c680a000840d94001e902809546446000d43c11154041801038a04421020b000901c0030f60200f8400c00120307031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 864595845 1250 864594595 864594611
    0x1082d012606040c050d0305041d070801060201090209071d0301090c08060702070e01050105090f1c0203010f0c080f070302040f0623090d0201032007061508070501050a21020706 78
    0x11100c2400040c20706000098107652406a4510a4650950081c0c50052480001d0b4404042c041d00445000c2c0c40c01d90300038051145031611009415804650a00000358000c00000d15070f401401281e0040358002c00720105643c4420080700d41a80b80c030f036004041c0b01264600d0380592003e20a0a00c2c841c058504664400c1c02c0281a61901002900c07503401c542c004003040105002100185056980903c0e06650320152140041c216412a141311980325108203010340e243c101c48000c1d406aa40f02340e00a00452040b1740c0748008442c0c5106507140441e40d02000a031741010f11414040c0c0c1b02940d4100107081588410480c0505440b1784c0003880030645400c24980368418070034401e0031a4200c20f4042e4036091804001c42e820001114001341410b40340d080200e045403038030400302c441d142241211381d12000e107401c0032001703020310040013686410145408240700034042a40000e90384180c40305441d050802204603002c0a01500160143c54a111100d250100c41d0000b040b00302d0080e0004600304c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 864597095 1250 864595845 864595889
    0x507060c091805010f140d11060403080f07050c011b020409051507020d02070f060512100905190f0614060706020904141e01140402071a0c120a0b01082d01 68
    0x700c69000044000690482280300740d85220160821648c8016100e400c0d91000011a405008540000f4010302c00441c2010001800c1405403d0342070140d0b0445000d40c000c5130054810300305942c0d280e148105001402c401505254101d6520b80c1d1140049503911000500030040c0350300c0a0785e000c8010780001200568255040008a01400c0c83d0101054507501d0114041d00781c2c41440010f075200d440d241e0000300d080e1030706007151004249044045c8114500712084600c28640d00151204440c98803d6015140301c4a1140c8000e03a81601c00841c040d408000c100001c42d0000701041702c500d0740800000b913070b1303403140d028021005952079440780c454100250000c49441301a0081c03800400c0280c010826100612103180680340261001a9500c2480c205204100c113501042010703401c100091119070f4031810001c01000c3c0c05a0808011501c400301402c05903148101c1c1c1d140054041000300f10b0860f1041d0200c0311b08040c45941d08a0f521aa80400c07150304000d0b4841003c04d80c4c00708555500c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 864598345 1250 864597095 864597119
    0x6190c0b04061b02060702070e220503091504050f041d19290c030606040b18040c0507080a1d18090d1404030b1b04170d0c030507060c09180501 63
    0x2483d40c900150549282658001b582d5040c0e900c5006030840d8100c02184030f851522120f20501c000c020800c441159030340c00e00903034a07484100198090070b41c00c0d0980c1304200049090305c0543d070380182200507002031503040001903c0318441d840d000d522143d100300d80c422000c000c0c6c0400d428801c0301d00c05c01c00b400fa040100d0f000001810341030304c4c070245c03081003401a140000d800c6e91019034144165202e44074900401c02d00d0081d50400c0c100c2c203000080c84200b01c03e0580c1c40420079a421601441056040d00d4112014003500c0001031404c0c034148522244280501e0400d01600040c0c6003103e0040c0b82c00d4001010400300c1c07170001c000c00041d04180048803005004103c0c0310005428556560301203a880820301c0d01c19444040d2206e8450030102c0c1519905443c2c010503180c6c01d4100545440d12404c0c204c1102c1504003110f440e621a1404500c1a240940d0014042a42503152103081041c02c3d1144e002415a1080034820003004150219418044075200214032400305c9000482d0741c104806070400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 864599595 1250 864598345 864598391
    0x312020d151d1e0601030f020f0c07050a080f060c0d020d02030109051503031309050c0702030607110d021f2a110c0603010b0703120b0d150f05040206190c0b0406 71
    0x59100c3e218100303000c0043d2980d07568001c2e0080c83d00241050251048000901a580d40c0b0303400d0710000649689590000180c0c0c0e810f540088880700c690315500c03480580c0d1400c0b00300c4250070940001002075180410000900142000658058034145140342c0c03250882e40300344c1003c0d080755516400c1c810a6400d800c40004200c07000d800035490030010514403031129a40703114100c10262034a001800ba040110180e4090130360280032a0b0072401d01442c00703021481c0d404220742452180340d50301c4002d0342c030001d0100044031080c030300304a00d48203500034040606911800345d0002d80c0590551100c441002da060b6084510756551903e0407001207d070107003004d07070000c8014402e510a00060000300c0d081811214050b5160910b90300b008500e11849000e0094111074943c09030042d0744040034070003200780780415070301181c03400c10003110043d0030070f03044500070b44010b500203a003440300b8000d01d50407a003100c009085906040041c02501c3e61000d5482d441100c0485132540c5408040903140414a00742d68 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 864600845 1250 864599595 864599611
    0x13150501080d030b010503060609041b0e010f0c0f0314270310050105210708010e010212012103081008070306020a0311030705120c190c1407030312020d151d 69
    0x104007002e61300002d1640c000600524442c2c40006040da540b60b8031540107803004000c18107082c1440b4010403015001211b05ca0069000c500310460800b409481501900495a4090203030389803510151011510b0b080c401d02c02180d8410100a402c041492041f00e0040c00b02c440165180d0f0004408280342c1800c88440c520505030307003400d0041c401c41d0344403690750410904c0c9003144807400e03030411019480d0946c10b07480801294039280c01d1811007881034004140c8000c2c034002580e8a6641d420700c9041c000010007110309144c0d101c00003480040c1c800c0c038505800c208107400442640707854031a402d042220a41c42101c0107640010042650361709400740d85c41500b660403055041d813800344e1001c0c18900c101507100400c2c0304c10f14002141c001c81e0000f500d00c009602e2a0f502c1d100ca80b01c4c0400b40c000320301c2e440103039200100c00340080664000001d265080c4c80d0f1581d12030712034040819000010b0740007440e10f000929101d141036505a11410503290052088207130b80b40c04105625400c41600a005c0c103040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 864602095 1250 864600845 864600851
    0x170703020d2a09080111180303040b0d020702010810060e010e0303040f060e121519020d090303050411100e0603150315010e0619060c03020c0a0b070302120903070e13150501080d03 79
    0x3d1b4104c182c640648850070040044040c0d08003400700000c2c1944203d4121100c43e0310007040d081c500e10260b9002c1e01285100780c94900c000e4a5444003c002400c5500c07607000010740e0b072203801d40103501c1201541d000d50341c0a011641003075190484644c200703415800036000103d0303c0f032a0030001d1a100030100320407101200542042812901940c600a43c02400d8040751400e110140d420010b0039812500740070b0886400b01300f902518035000740505000da40c255040701000364405003600d0045424081e00640307484081c00260346030144806508001d03d56071000144411182c0c040e1410b02800704200440641e1070420740c101181c120400c4000f420b241d001c0d001c901301440c4400440c0051030151031407400c12003060319039842c0891800701480e11898001d00701c0e07400060622403820142c2002c900c0b030340a6039002102c40c00d01280c1801805655a13160f0721000080000001c84105540c1152040c10040845005038491002d00c81112a42000c02e80d030300c2c40104001318080c07002c0c503100600b0345018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 864603345 1250 864602095 864602111
    0xb01030f0c2003040306020f0d0e1b040902030a0b130311060f06040906021e040f05090c03010e060d0f0f0605060105162d08090103060501170703020d2a090801 70
    0x700841680607a081041c03140d0b200005180c14104241c400442c0e01040940d41c41c0c0f9859140d1009401c05408a031400d41849c40c942d00c24440480d0300c0329103240401110304072003403120410002c0c0101c4102a6014000c410006010428880c0b049104021280e894900b040c4070b03150052690050b0040c0710120780204050144040311507004070340040e0200c801203041c0d051410702000900c00c000040501d00c482400c482c1304240408094011607500c4040317600741f07036519803d112800d14200e40c3e0300c2e01c0420420060040c50748010b262070308150040c000c44452061a07448058080e5500c00640e41411406000c3d001c0140d240525503001d0000e103000d50400e08415030b07403000f50300f400c0c90081041c0e4040b03000b603c0c1000241d05681620a0744103105546061b06e041c0001c09610004603180001c0c248000400d031035005131250344c0034005803000f0314055a24a9002c07130003900888031015186072640c95202c010400b10707004c0002504000e0010000c42400000941002c3d8150303c8000180d050041c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 864604595 1250 864603345 864603347
    0x3140102090f0d0309030303050c0d050711011505030c060d0204080313080d1d010f03110703110d0306081c02031b030c1011040302120f060903030a06090b0a051011010c030b01030f0c 80
    0x7605c101d03941400d000c00c10703490307100e07041007940100881805818901000c000c82d0a40c01007440f40124581d000030060481169a0054140914000c142c2c050307022100401e102d007001d0b001803482407102c1ea0b00504040c1c0701d2040d0350035503008a003403140e01010500d0501291000b800b010242603010305094400304051102d0010034440e0030300781810f000015800006083c080e800c81100000604070003a07641c01d00e484d002d820f0461401d490282881441d5982c55064003038440c50043e911814000c01c1a00c5122400d000d6121b120400350086010500035510034a80d030008401d0f0000c4024041d5845020108006281400d0701a0139080c0c6420b028054440700a454120b0301600c2c0c056440d820003041c0301c1c1318035191444035850880c00380b203a541000b601d520301102a6008460031817041c0b2040d5940c003219003d0302c520b400b006511203150241040907180c5a06511400701c0035040406030560302496403070031500394000301e8020030740340c0d4240040c2e5a403600c80d0300340000460000304600e01440398 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 864605845 1250 864604595 864604607
    0x1b0f0d1107150c17091509100615020c090a0605030d0504030209070206240a0b0a0323011a0901110d0f23040306050c0d1a150a021506010903140102090f0d03 69
    0x6400f01000f0b242d200131400408080c0254041214111444040c40c101040c22030781e608d0742c0548c045c0c401c614100e80401c2c00160b0410a038000300856000b040c215000108008920a026101e1400c0355500d41d40058240c60501105681009036101d04e61520b19500510218000c018040d0b0210340141081218120018000c00072110081001880711813064000c00c401c0f2001c0d07000301c00518000b04540c60380c103500d40c2280c100ca10030600030101040c0300310407043c810042030054407111707070b00c42e600c800c5006d013254081c103d040c10515185110b120004040340c140545c501d02900020a2080140280780c0c104c050384240070700c440303481c000b43c16881045029501031070000400140e165000306808111603000c0ea82d84541c070304020000200d180d01202d580131906030006008000d54501c540c102c10100c07043c1c5825004903009411104800483d0000c142401040c05c3d0600c05e6419010001c50398000010100c0c08034503000503601c0c2c0499003000414000c5041a0344190298540d40c0c000035030000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 864607095 1250 864605845 864605867
    0x50a09080a0506190b1f090306090605250f18050d0b010f05030d020a1502070804090207120c0b070e120f06100b0703051215060313020114031b0f0d1107150c 69
    0xa040194040402008403a99111540064a01c030b0511101c3c106000d84c0341d0140c1e00602e116900008a400d005403103445050591a54002041d036004004c1b3b21f1380d0240e104001d1001d01e43d0281c0000b81c0e00d038000200014040c010603a12480008018098a030b00120b10202400085004000010b4992030095031112010030040c0400000c8200d02c660f0f22444d0141d880c00d80e40114016111138540851030000c3d0420042541c0008042c004074150600a800f01c000942d0407143c02c030b0f01c1d51744074042503801e81b04d500c1301550001c000c2d404101480f0000c0c010b002d1110604d10140009007001e440b202c1d414070442d0000c080002040080384000313900641210241d2821101c0c00003030795560b007030002c3c550303403d118026007000b0000b0800440f0685518083d0605c2d200b6210705481d002984030312003c5002c1142c0d65683c0b40c01c50944100c892031068042e08202c0f0700000114038000604505800391500e00c6035007403181c0307004113070142003015010394a980e15100d21010081c0440c00400200054208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 864608345 1250 864607095 864607129
    0x705060403020c0a0b1b071212030f050402090c160204051023030d0f110d03050f0a0b060301090911030703050703021503090c010f0e0d050d14090a06050a09080a0506190b 75
    0xb01c000b00d08507503011f0201c1c10003401940307072a401d51100c1d814004081c1035103454140002c1d00d07000c11180c0e003062034401c00740101c2d0041c0850b8040c1d924600d0114084d03101c001c181c10c00d0a0000f09400c0181c1e00e40c0910703446000c1000c049140107207040e5080004d01030240c46031400e040215401c15254a00242d500d81649030740c64442c8200c44144c00075103550b030038504140d01501454140001e00c541640061380507620114103888a940c9048080044030a80300410394416410401041b1100b480c0d08003c6030207000d40a604180f0380c1140000e0728000d00c0b80e1040b28540c10906041041d890a21030300d84000441014003442e41ca000040551a406400d04907414800148108507500c2e04c03508025080010190070045092018100199600101054100090084130150002d0108482903880540c2c01034607030808203040007801d03110f07600120b0300c1c01c007080300105000542000030080580030038021805048581490302400303124481014a4103c80e500341004413a4a403102d80008030801c0c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 864609595 1250 864608345 864608377
    0x10c0503041e0309080d03090b0603010b0a0b0d27140307050a030f093201020a020a03020f0612040f1205121302032d251a0403080705060403020c0a0b 66
    0x280c582603813403518a4100d032501d4424900d180400c00e405910900a0030f01070007190740300f82c1d1200109802d030781c0c440201a400a5a05200b0007110030b041000d41040800030300082101151800104e0070040c0d124040403104d94012a070340709020354419041011130300e00011310b1074007006458041e0f4a144200000302041220406080224450182c500240c011078070350308140526a020f661203007868202200559031600c03e504002c1d8000139441c030780c0740c2e800b402e0b00703081c540ba603000c02040d1449101c0d4141c02c850100f28003c404595507200c10701c076621521507000c80400a0801043d0703118001c91490912600b004820031001d500c4d06c030301c2ea00000c000c0103003800d049030384003103420401d071420b003e604e20742d2806a0021901001d00180b580311900011038441c518201c0c3c1c0c0712807078681e4001204103451012018008041d80c190f928401c0c038048010a46416505e565030080b940c2b180c1425113080d0840800e0108040e4140103040f0708003006c540c00041039084c0a0108500d1151030080c3d069080c2d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 864610845 1250 864609595 864609653
    0xf040206031311040c05070b0c0307021515061c0b0607020a05100c06020c0a11040207080f0a02010b0603100e09070503061f03120804120908061308070b0a020408010c050304 76
    0xf5490b451080080600b091150307034890003014105420110007241e00d13207600000106840340c07103000c4da403203052607a005200c810121409501c0c00c04004d040c07201820b59042440b081a1603003c010989424588011003440c2410340c1c041048824042c003843c4a080108028005070f6142a07608050358170865a210725100700d82010303103400d00142e100401030b900128960040b0342001c601008a58090315407044007400d214100b0080780300c0c1311b81c010701da90340a00a000d42c000c5480017806403240640000240d1100d220001803a980003200d01240d420702410003030081d04020482d154200d010900208482d6060100081e11044009e2002460203000c8499407203200d8074500c0340c402150411803900400d01c4a0100a24002040700c056540d481101420002c551080e100c0c4012100410041c00c02915078a0a901500340c001c4000e503046c6409110601c041560800414011011284016aa0f91500941d9070964010580c1d8000b8000c09000700408030340b007500040a050381d01c0c1800c0c000b01d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 864612095 1250 864610845 864610853
    0x109030b0a0f090818030105040f0f021201050c0a0e030a0c052403090703020f0607050a0209100905090706020d090b070204020d18050a060624082215050f0402060313 73
    0xc0340703105a4003c0c2060030801c00d2084680c0241905011081d688144202500505003038800649006020252030034146004c510802400d072001ba10080c4696540f9403014000d5007036580c1039801000c4c00f04005001360107250807805149200070142c0203071000401c2038440c2c0800d50203610500e4014400c000c81088410500020b141e501c6103810300b5552a030038580d01981c0d8482841c00300f01d016a1400300354041c83d14110056940440e4460000c003100c0750141c1c00d101d40164017502942c0c40c8440031101007010380d4607014140c41140309800400c034051603d10028540070346420f405082c0214190244011603005e0200c40c100341c1c041d80c0c00350780e0303140c841540f00040c203a04003142461121030382e10108011012400c940703400c0c000c0b0400d00080781c994030450060541e00040310a00c107402003c64140320300542030558813503c907010b07003000c000c80034030025880d400034101154007000c442031920003c0b0903841280c2c1c00c4804503403204007a141590204403d440080c0c107480140d9100e0032140c00700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 864613345 1250 864612095 864612101
    0x13060b040216140c0109081b0d02061b0705061e18030708100b19060f111209181003031107080312012408151504060206190207020109030b0a 62
    0x50030700301880c0c194800040c140f00d44000c100e0880348803070703000d0002000160340c031402401c4146e4403004007a000c615005444903004096500b01070390081c160404081c050780d2013802408582055151040d2280384044441e400c1c50b200b90401c902c034400501c00c107840450132041c22000234508612580ea240c07480c02c0d00100d004003030850280e06100e40034020503020004206403040b4512001d040c096110803004000000c1c2d01000c1180c15440c5a035802c000c0715220717440140c00790405052403a202034429500505088242205160a40c1d0000f080c00700703814014403d4030b80d81c1d403141d107038095800c1c4182c034031f00f6655442c40044c007040320f0f0705100240c20100748660401002240203ca58448030700c6001413484509205080e103004a07850a0b082c0c3d00c40e00343e0402d24032807550380d03400c0d56655586000082d014107070b440701c0e0f007022000a00d594400031355001003019200030b40081039903261035600302c0510440302106103d00c9006000010050f60081c0702d02c002e4a52021400311295a211408001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 864614595 1250 864613345 864613357
    0xc02030f0102030403030b010f0212070f0201031d03180301230c0c06010905060a0512060f13020402030112050c01020a150c0e06030a06030312020a140a030b060307080a0b0913060b0402 81
    0x65502c00010301041580540c00b5080c2c003002a21580152004072905980710250b12905005540d410001200021441c0c4600d84020f441410700003113840d040042e208848035208000240e9a1002031842c140c2101c140c200d2a8a0310100e0007440020307007101030725086920181205022020b640301094501122a060304d1400350540120f802942e03440690401038031003a82c01034040d8504c44804140d506081c0141c0040c194140010401501e0740039030f485031510b0007807148200080d014000d00061350341b030005500a28200c0e0000390280038a090a034140840708058905660041700c0381c0c00011100b2003004004410448000b51848107450140c0f126002c0300071040d80454000100128141c0302c2c2d20030810707640265101c140e000700300c589980403031003041010404075030000c0d035404003901e40324010502941c1d985004160580842e02007902904107a40c60130229041800704170480105125003c06180d0480d150200c0d130400340041810040e4200700034104a4035140b440f1020780320364044405c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 864615845 1250 864614595 864614623
    0x90a121a040303061a071211010f060e1009020a020d05090613030f120f020307020f0a0b1303060507030921030e07060309050601150504051009031704030203100c0e010c0203 76
    0x209034070340303854010000c102c14040c8410f801c048640e403048100410081d076114660021341100d410601440079508040300c1501c60b0020343d02c90300140c06951b082e01902c0d00404002c0140c84007030134080d00042060400d42c001005551052005070b80303542e8000b031722123414800390900d03079681c00b03515010030602d00c5801c080c4c40b0300124501001081143c11010700700510f0107034610b54084617840004803030305c000450145c03005070320a000c01300261820804843c030607807009016560095a0349041103040d00552003100685207201e500300700f4031415018a41d4031060a1504000907000d0b41da6414600f03006440900700b0300c2d130f403044205071240282c0c0040c0d0090401030403203030300640e102d400402524100030b04031160b000e9480001910003010300940540000c5403030f1107007040e09200030f2008800742d040d202810080e5140c0000085001c44045420341c0803210079090b40c031811801810714105800340c0103a681032038111807100896200b031801e84012000d18180c0e01108c403e000181c42e010319130000c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 864617095 1250 864615845 864615893
    0x50d060b180f0f090d0f110f01060303140c07030312140c09041401053a030e100c0c03020910081b010807080103051f11131406090a12 59
    0x840c88140078054840e6442000b4000c40d60b80c1c0002e02600031101380c401102c41d80c00782c0e0100d00e030781c1e010304052000524249000b9805104c0038080a2030001200882ca0b16039641d04803c2c0700b8950700c0542d8000c9660b40b4a00300e40f03400d005040380c540d100d5540c40050200320841040c903000600702d8014601052100340284228102028401200c1d4400b080c000e04c41c1e490100000e8600c003600c031007a812240010f010442016801c102140d548482d06200c0800300c803d4140700c48403c26845092420340d00035500c01040c0751080003400072400164205d601808000e121410000e141021800d055960545012680d40c1311725480d8a152074254020090343c2c082c03403c0396001c0314205801c04042581c240d9030001651a100c8041e11400000c6c0000781441d005121030188007080010f041d592000e4200d000a0020110103280324603420544541007440c2c0142e404200610300407002041c00b503011190640317014411740004410101a11802d001520035508000c28042c245100042c504540c00c0c202e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 864618345 1250 864617095 864617119
    0x150601051b1515060f0f090315010e07111b01020c10080405011b02120a090e090a110102070f060804051006080601032112050612071d06100207050d060b 67
    0xd9110421030a80c12080b401ea000010348502042200d44140c140c003400b82d518100741101000140e5004036070a0050040030480f48400362000c00c049070240c0d0783c00008603401e505200082200c1c071400b525240411841c83d403826861440031405d604140c1d400744250303255180c10710050341424035100b030055200182059400045401c481143c0c0300b80d108a008011103581c0d50013900d01103042d041404010391102810800e91606080140358102c098100315204a540d1244c1b803c24500c11a2000e020b40c0080421808021400d54522103a0100f4000703029030354101481041c9405c4203110b10b404220f1008007250510a00344000c0d14100411881801495181c084056940c0c1c800e11084503205101290507003981015540d80300c2411466407802d015008001403203029100250844d0761094500072031601407041004290020905040d01c6810b45049011540001400410b105d0003a560016501c030b40310750214040c02902c1d01160041035070005410184010001c541025030003641c83c1880d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 864619595 1250 864618345 864618397
    0xf140a0f210c0509011e0c08030a0906020406170a05060f01141c02040e0106050f0d020c0316050606030d02030415031509060f150e090406050c070b011d0f04030215060105 75
    0x910324248281c8035207003c5000120746e240d5807000303480442d000804a10f0386800142c3c0880040d41c021290980c040703285912078482c6030807a8491b078404d60120300302c0c0071065000146204c0d40d0394052001070302008203203001000300b00030700c40c04101c445c100700200c842c000b0140d501d6000d84040d41541c0e6080e03041c81035501444030081d40980200b00304850130400000d1491320030340445e203080410b004990304150704111504040d401c4021501c003240421f1021450314401d460000041c940240c000300103030b081c00030038141800d8040010400f15001004140544843c1c0c0364200b07441e40181c42c000940c80c8044118441c0c0c41d405070000100c0078180780303000944030381c0c1c07003240002e480207880d007081500341141013a02d08142e00242c0c0c40c1c10170510000035000c21540c0e480782e90702010f00310046140c134040f90b40340c0016481c00d030000301d0025900094440600d4100d10442e902610321280d104440c14070380c030041e5540380116031048200d030200c40050301c2c5034851001c0d9211005014883e51500451981c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 864620845 1250 864619595 864619597
    0x313082d0702120613020d110402131e0b0912072d0909020d0b0415020c010204080106140a120305120f0f1b070807081201060f140a0f210c05 62
    0x991040f41c0c0c044104410100115030140182906601d141d000901a820302c039a0050086007910585d1204040c5695600e03280000c0185410b10080890b41c0c0381800d168100660307000c010007042c402100c00501c03008842d00200c480c5410102c620149040c0c8015000c0c1c5041c41da504446121685121a081a00704001c80700e40c1444c1c00c2c42c20a0400c0d51107170740c0202290004e00020350310441401056001c40d16900076075400902425070815501c100754404811380c0d0080c02409001c0e9400101085071a80c01e12417138004c5d000a4024019003680140080c1040c030a5000341d50b806001d5280c2c810415010f40201c64132040184c0c036810301450301110b50b000741e00040b20031040c0c1c1c4001b02c0025180000100070302c0203240c10441102d00b000e4894492005a8001c5001122101010484001c034a03000e290101d0013403a0554844a00340b81d400001003007000241640103c49400340000200e881d00901d614070342044906d0058041184030810300c3c41d8028035070340400540d117009898400203034054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 864622095 1250 864620845 864620857
    0x31208040b0a1b050c0c220b09060f060c0a0b0c0901020f0703051b01020c060c0c1009030c0506030601050721170c0906030c070501060e01030303060503030313082d 72
    0x1100251550741c41c0200001c1d16440c014581501d10b0904000b600c03d0701440142c41c001044104840f42c0c4d401903c049800d40c0c0c2000400d00381705401703084401400081d030003070842c80344050350078105904201000c100008100d0210390700c070380760128240c8001c80040009810b859008072040802c2e007080c07084075985074410605a0700502400c2000103c80200203440001c8903401001815001100715082c4140b408240440b41180282d03581d05400799521400b0700120048a03000e410040d00c543c041001545c900322090041c020903510400204406411500440d0402e540e080d5682c0d0b110704c0125968031500c5001402d6403500500781811000f401240195400c2036200c1001d200c284a40100e031311041140d502c0d0030703c0d0003001104610b00b06080070359008a402004142084016500c070341c00d40b442c0c7d41060410301c002c4401041855130500a120082c0419406984ce60402d0307454081d0a50040c072001d8240003000600b0b0300310316280e4048146281c4c0d002c0031500c0160610b60840700701d074401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 864623345 1250 864622095 864622103
    0x609021603031d0303041b081b190e0103050304061808070e070e0405130201080903090a031101020a14010203060a0f0605030a0504021f0309060b0109050d0b061305010e07090605040f06081003120804 87
    0x1d00001314140d200001c0c0803110310821988000f0220103270f002c20120b900200e49111887c03915200008110880b2a411406140300d030b0050760303c8506045c03005000d00403032030722030340100502e09080000c1034000c5000b0303040d00d203a000046c8184c0d481c054260740d000c070301c2034000d81c00030314000800641c51030705080c100340d0520036603814000c1d413980364595589004402130380303901000d280c1e001c00c0082c981440a000700f40e01801600d441d1001c0317440301420303001e10114444042e5000001c003c8203140c021084c0014100e4110a0840c40d82081d4005000f80030045c4110f00146e1340708046000d43d5207102c0c48004910b04d03000c071190500d0300c5040040240141071011034483c2d08160315036401d0340c0a01c10030702c00d48034043d00c401c20380911625011404c0001420362074001b1141d254506021a1138045c8a010342071031518401d01d41070805009181d8103203036112000300641440300384141848a0340d840115a1103150120f07072074845084100e9200e0315640000d00d01300e00a00421819904120301c81e11450003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 864624595 1250 864623345 864623393
    0x20c210706060f26150f070801060c0b0a0b0102010b030304060201140112121d0409030905030606090108030301061d0618090903160f05031207020f010609021603031d030304 76
    0x503e4000d0003030700f0b00c1c42c0104407020035082032001c83d50203058031150b0024042001c883c2440b2a45804c440c4a00090710841d42c040e0030b480402401c2078000c90100c2c0106460b140410030b881c960b440307100b41d0b00400b50015040343e07111200320029070700c04d400240c41c03c038004054980d6142e940f00042c3c000e09480400e05c580c0715070040000750589002d541803000d2034222907100d9080c06074034022035601d2914030015200340c6008030500120741300d078070039640c0e1300b8802e4449404e5142400100b41c6000001000382c1d00c50302008005001018010060ba0304550690510b05540c10745022900b981c1d030350b1218825006003021584501107114088803208000050b55025410f8a0355901d2503100c0c4074010321304024880300110900002c20f40300c040340302c050113902982c1c2440c04d0a44450f41d9201e05490001c0107900ad109041c0ca400070170b111729002003a000c4030031481c14050341030288002d02540c01c0602415502c588558140300e075843c1c06ca0301c2c0000042620398924040c9085000d0300003c01400500202c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 864625845 1250 864624595 864624599
    0xc020301141006120e0c01051606060f030c090911270405070f0b0a091421070504050a1406060304170408030705010b270c041211030f060712020c21070606 68
    0x1609210b6500c5e0035103408003504150000e00010f4405900855a8584680c0200f102c0000b0801d075101e0b03c00a0300030b655001a03c54030b503083c408080300e03854200c0701e807491801c804440000c240442c0c4a64408055401da1000c4294000003d2850ba5150101c129070492002300820818082030240a40340d001031038401142d120450407096020702c00d010008511103180078840743d200554034080961004054860110304e00006c0400c2011250302c0c0310341c581c0071320001d00052a090086a500c03210b03620040240368100c42141c0a030000203401c0a005d40d50010104090061079551480460340c02413103265210741e15408543e507588019811b0300c0700d51030082d9040d4103150015025812801700c02c1020144480c00e401d8100d250320180c0800c4012004001c000ba4405a02d910303d8281401026000001c13800b2030300780341c2803000810001181d90464001c200f0b00340d0300300c0000140c26002003001a02ea22a45036550b03d41b40303c0441c400150041d61000c01051400c1070014401e0358864981448159 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 864627095 1250 864625845 864625877
    0x3060d14241b0a02030a031e110a120b060a08060f030109030807091203082719020406050603010e040308180a150c1404090e0c0d0303020403120e0d030c020301141006 73
    0x4001c03c8584801604100055003420740300fa04401480780f038482107145000031180121041365912400784240c50400f080303140200d600800100421604000c1c180600f0010038000303a003901c030f200c5011060181c5a40403444076103807170031404000c0c500a8000c00c000303600c50a01030620700e4101c3c1d4100000340c0304440894030410031040d4500e42989030f2181201c680314030070800402d0002c00e1075410f8400b803521640c450400c00300071400310308020350030206035601350340144020b54500781c001d0360141808000400c010001c10100c2544287c25141c540d2907900c641800304145200c200b0440614419894000b0921072241d000e1054940840820004950f015200341da0081225280158650041c80f0030000184660003903200002d02c0b01c2a80c003a04c6021000510104d880d440940000b54040b0b018000c205c0d003010084540180c500b4034020a014007400519284580000201003015051002c0700715107094104454480d500da454085038070700710820321104d145030b22561000030020800403840d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 864628345 1250 864627095 864627097
    0x603100902010203190c060c05040609090b090708040f0501060b03070f030506010804030e01021006080a030201150e01053c03010605040e0a06050403051213120503060d14241b 77
    0x5a410f07005507081010038103800072600d12010008040c8014448000b00040e141d22070035018080a403039843d1180d0401c1001402510307e0703000394680500d00b26140c102a9107040315194090540e03e41b00da9103688070300c0c000c0ba128584280c010001e40c00c216010500740780c0f800140d81300f5595030b0b880c031880e8400080202d00342e950a0360742c14080740300d10b00440e01091140c4a80c0490301d1b41801120051341d07510f2810710480744c4a9122000c2904905028010194280520f0400c1c01c041691780c01550308017900c03065040c3d4188184c41c81002065092407200409010280e890140c4440d0728071181c600d030903031603035070681003503860320a501e03014010941d07103000c0c810000500550802014082d5080c1d69102c000d11014100307509200b400d1058101d0302e1700001c00a44200506118504001020324103000d0401d00702003070350240441401000341580b5000c06c0c5190982e0041445805c1c0100301ea05d082c10300035404920200407135a1040480d4038410301103824090108440e0345040c02e0848003811400e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 864629595 1250 864628345 864628361
    0x1e0601030219031e170d061404062709061a090a150b03040212120d15050d0305131e0521030304030c141507180b0f1606090506060310 59
    0x6000c1404010901001c0006006501c142d02000541030b800c20120401d40001c00c0d03440149442c7c002c18042400d0340b4400c441c0c58002a10b09102007402c01c24054850900ea041c209000620203000410003c00ca4200e03c1c1c0c600d800c00010050050284105d0088401c50140c1c1c90040d0265404103800d8029031203198030300d68040752103402090914481107210b034006442a40c2c000110400d00324086014406916290012540c4543e42c070301d501010015643d0302c0380700f1400c00c80231007402c0151b6200e42000c9040c0c50f61501d01155126900074036000d8500d0650840e0000304103041840f0030342440c800c4100181c0c0c0c2c0883d1040d05043c000360010050f50b02041043c5500d4000340046400603010b40280740040d07200789032030301000245c3e901d410700c1c00100c10000213030b002d540d4050202c02c54001700444954448c1c4055500c2c02818017454603054814081d0030841d05000281400e84000201c58070113480d68003207424803844d00704c1d081403a0b03501d0095418074888e01507007a089803140c25520030900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 864630845 1250 864629595 864629603
    0xf1d090d1b1a0109050618100e04051c03270f170c100f0506010206040201020a081e180a0f1404110c15150a0815091e060103021903 58
    0x6003114001d14004a1120900011220419201e0103600c0c2422981c508a01a05114000113040d160000c10880d60071b00c00036007100b10591480c144030018660f0300c83c0b142a209500300140c150341b52440d05602c1d2891142010f06610701d4802d01c091402d9242d0031030001d20b00e0300d10b4050340b140184002c41c1c2d000b0f54001300003031003001c2e808a000d00050b1382107150702c94000d0002c071300b03400e007005100c0301801c1c04151f080030140c16540e22040c030fa1018161050640001080c030044c10186029070001c1e503101c580c2040940700c00070126980000400b1100e0b0f40c0c00210010f2031366511480c1206e10002460140681503100f003010400c04034840040280b0081140d50842c81c4d120441a00307401d0100500805900c50007900040140a907080400c00203590480100c2004124900e449844005500b00039a504c5224a80c401c504110441e000182d00c0301c4210990b0100ca182c9e05d82414862806504088a031801140345071208078402c804a48a4103c07802a94616203e0038a00129a410001404010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 864632095 1250 864630845 864630857
    0x140a030b03102d020c030d0203060112060302090a050c041e030510050c070f020402041a0316030e03090118030212070305010c05040501051206030109080c01020c07120c15090f1d090d 80
    0x42d8403c003104100760307030610b403044005203400d603400c18503411075000220b1400199000028000700356805102200b00701d031511001c02c510387c1540d0005085041c00b500d0480b1007500c440c042022010b8480c216030040020303074038400b0b100f401e08460f0790180e101403005403198041c0c2c0070000040b00342c0d4095984181c1d4041380e0307549088266551040b4560700960300b03a070425420304c80411060b10658207495401006822a502e81c5086005262000c2103061000101030500c1c0785040340c408000107613070380b0b00c070242486500078003854001005a0b0099101075444030828400c00c00c4441e0210b088030590340a50000d101100780380714256014410740c0300310790000d0700801207015242e003006030007504500001c1c00800c03030600d40c2d01d411005802c801031201e66658000b03210008030038100310700401882107001c5024076180c56118104000514410503454000c40c0f104041061712481842e0047d049000c0750048041d01d4400c00c00c003482c5200309500e2000c40002c08103100f1700002814468084a6680310 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 864633345 1250 864632095 864632141
    0x40b0411041a12012c15010905061207050306071b0f030302190f090303051c1506180b09040b2202090a0b270604230414010f1203140a030b0310 63
    0x10701c9030b00c04c12170b081c1c406901482c0300038040144007400e0903000b04442c0348003091600f0004104224100081041d44560348886400c01246c1c4012861540c003034a036040070a40760040b401590041d8900c000010038084044070550704254059003c4c0c0703084205510f0000400003c603e060f5544c00302079aa00000c108034640030000079210710001c1124a43c0c040180d0307c1074000020a0003175401c589091f148690300c0d10720500c860f6600040c0c075130072004010b10301c4148a141079403165042c400c51030a1400b503600e40c031014081d912102c802e800380c2c1036001200503806003880c0e00080207400010985105440040000540c41a04411f6410303010150442004040340320a441c214002c0c0e0f0050300b900308405100c001842c0c91480d41118a8112000e81d041506020904120845020322a80400c40b1400001480032001c208450b030706452038014010524000c40c2026106c410300910702c540c10400004100340c0e0305615070400e410302d407400e0b0200d480c40b420250f07103102600c56040300d140c0c040040c1024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 864634595 1250 864633345 864633401
    0x40305161e0e2809150c05131401050712080402100e0303092110090501060902210a0b0406090e070527040f0b010303020607021c0503040b0411041a1201 67
    0x1e142d403195451608264450354011681040e81c40e82d01056804c6a10b01221005c024820302405010342d040d80b030071600d009014480c5110103050b03409142c1c0100404400300c0c0d0300b64011070031a03108641156212400441c0414020403c88040f2812400740483c02c0350400e406010f0000c0481d488030040256080290131020b01c28820213407a001c80d40e00c2d442200d2881c01002c14800da038420916954045000c40050034000d00f9140a580a900054410840d00b00e801d541e81d501a003c00300d98164000080d1201c400000103403044101040d84035180210000c0c080002d60b0040d564544484192140c1d5a9114208428103c001e0840c4180075000a0001520705d2100c50203a440f41c0b00d4484103055010315124040c10150903001100540e1190080c070641c245c04002034551405a501340b2210700ca00c0903c0280240070280009000382c002002103010041c40307003600c090080c400780042091a604409a10f0311880c1035000600030000d034003104480c094103008181340000c540c0617000c081118400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 864635845 1250 864634595 864634621
    0xd0c0504030b011211090a020703080907080319030b040c0f030e060613180f0f05070e1b18150d0f0603020306010b0c0f07230108070801051302040305161e0e 69
    0x101c21a001d0b221807017480b0955880b5001180a001410070040e15130b501890b015010403030141500f0429482102e003040360107400011100800a41a5601084100c2440030340c00340c0721841c2e009510078144403d51b0342d2298080d0355100681002e41e4180490f012070f0061035102d00060354a030b6040002e007107404000d585640c0200d003000400c0c0196440c040201d45606400c1e81e030301c0e01c084a01c29060007070344003448800c101071801380503000d28586480c10051261000714107100e0007070341c4060012404183d42d040f108072b0100c0e5444081d1818011039101c0c0d208050710390016180d01c14052900f5000b4500c600507105400540c1d90140c01480b959081290403c91350300703c0c99221361644211716007101829002d1003103a00038000c02c543c681d00c8810307514621800807140050541000841d4040100c41544420b90504458054412001e004012180034010744038603040a05103100d0403c21071101c1210240a0f4103e03100400200c2225914882015206c0c0b050701c98025502e54100114903500030240d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 864637095 1250 864635845 864635879
    0x21120b01021002121806150f121c031a0114180d08090102060705090906010f0917030903060108010b010804110103090210030f0c08100e0901060e0c0d0c0504030b01 72
    0x401224102d50741421518141c1c1e001000b414801c01044007400030f074400c0c0003040b0041410300310251140f45000e40103d4600e11103503142611510f5110300402094413080c0800703034014040f2083e075114112003020010000c8014540310000391400c6202190104001426400000143d450340b075010002d4603120455044000d0b030b80c150b24145411800d996a079040d00c1d44000c1c0c07080d140c50f0707141c041d050300282c14424000c083c81c0070720904008000c3c04e07565000240d58044824203104103244100202110030304401d4014005280f18401510a04031000000e8445108100c0c11954280e882d5034510f4260340380300107054086403164001c200025003e462203001804185000510540e0b280c0025600f00561806a00402c1c2c2e600c07144031a01c2d0060156a540b1001030901409a00340345241842700c4015119844503881c03881c0100d11400341c207410405c000d00d40a482144142021410703050150302980641c00c0641c87d1013681c400082c00342e82030701c08603070b01700a410803a41c0ca801c1031307043c07288800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 864638345 1250 864637095 864637097
    0x30a1b090510140f070c090506090c0301030602071403210606040510110307022707030e030d23070906180b181f0201020306120604020d17120403020a21120b01 70
    0x920602c191a4030071380c00343c0107941c0140009415a483c00c01c094003220400703484180940b10071010459118054001c423411290301910069a072811408c08408207041c400c6541610b010000d080d1070503100103005408086000c94100f50f894a5010030001c1c24070983c441c50341c10000c2c030384c0b1030401c0b103000c0c00310680301c2900f04040d280780c80407507070002c0c207040300d02c007800c0e481781e20342c1e80d118150030089816007139200c052410308100400480404a40d280201244180c520361a41c0ca01109140c102400718181110a01550050708100e41c004e800003080707002c2c1d076000514080901070440e00000d80102114201034080c0d10340060301029a54440034a4038142d041103c5c50b01003400b4803594903000c0c007514042c2c4c0c00144c403801c01c441041540c01124058204c1a4013400620000d80d40e0448240c1c00b01d588280303000341c01881c0442000c2e050040182c68403d400461003080b041c103802040300e401d140d02c1102c0742803070005107156070090500e0403c90f2000042ca944040c01404d406540518500a81 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 864639595 1250 864638345 864638347
    0x203090c01052b3303110a0b0d050a24030f0c030506091b010c050c2e0503090c0406030b070c0501200403020a060201090503031317030a1b09051014 65
    0x60703c40c4604002c0000b9003800d15a40d4a00440d4651001900201c4890062050f008000081c600d08105080300e8000135198050b40d07203080846a403051260001808081c21036511046003110300d82c01040c080303400c480b0007030600c10750f803441910030303a841e00343c1112805030300c12110304507110a401c1c24141e540494110b4030344100800860010054644101c142c54020040003515000340c418001405a24078148044418810000756022070111075001c03007a07881e2902e200d841d0030290603103a0700d4087e101002c200400740c019580c0d0b2001c02144141102e40442d040c00042c0c01c10301040360241d12001d070a500200000c6000316201d03515031034409019100100f59448004010781e18040251201d544c42e034400a020002c5080c411004070092019000801004500d6211151a844003c1100706515080c04001e020080e0501100c840b01d0802c4482035120310f0942c910600502d1000000180d0855031748a28200a10522622054a0015184085524181209490642c0121010701013428 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 864640845 1250 864639595 864639637
    0x102030702061602011e0c0605060a051903050706050f070201050c0a0c080c13050108031204050304032405160f03020a0203120f06190b270315090c040203090c0105 72
    0x1541c1009440010000d00c6010f00c8203110748009031402d40881c4081e02006421840c82078915049900c00d00d01390782043c2d022038180c1e28400040e812842a070400ea51001050a6401481c542c4403600e00c244d922800c100c4140b90b03180c003419192801745100e191840e0034100700e0f03c401035110704098144907103280c0803507100008036500c40300c0302c2c142504201003660190182c0c50039440c0c070301000c0e000c2583c130040420265041c4882c142d01d900c81c4900c920300203100c1c54041020042e04004603002140c1102140a02c2e400c0030300a80422402d5512030b8440030305003404115071a92043c02d40180c03a000f03464030f250082c041d45094000e9082092000c2c29400107004c0b505d690024044540d10900080b422031000303180c58801c200d0f9040c803942c000c6c0c410b100c807044180048018882202c4400180c0291800105003003e002400c0a0000c05046d4250190032145180c0700400324441d4024034842c0c1c01d84451010a40c20710041380402c44000e0b4155100d070708110010f50088000b000001c1007011484d103050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 864642095 1250 864640845 864640849
    0x8010b070c09091b08060a11070804060c050307060507090e090f0a02010e060d09050304080d02031213061d0a0c0801150902130b1209060a110a080a240f12020108040807020102030702 80
    0x509135038010081c6411103030801c40001035900c2030303d401744101048c041c00e01d0425100e07400540141d010388406e2041d001c81502c24400708005440d0440d0380a07070144a0ba1501040081540c07600b8842c081820313610301c0100b040c0c84000f107000c0440184400c001c2c166580c19070011104043c8103010039800450410a01c2c09040c00303401035011940c0140300456a49140181607480c000d01e80c48110119001030045021510f41d101c1c03620340010502c50b03054038072000b0703045c444001c000c81441c1d1400c920392403002034440440450114292800703640e0701540550340300202400e0b2000045004510a100700c0248001040f660251115071801c404840c4510780ba240c184800c0c0d40070041c0c0d00d00084121082080c104c1080101c00c1c2e10401c151010300082031080c001504a01850903102c0c1445040303400900c040c0709652003249100c8420421611409900303e55101c080414026250390010781e00c00030960021101d900d0340101da06070740e0281142e44e9074840f60410340250000b20b0441c003003080240050307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 864643345 1250 864642095 864642143
    0xd12110d0302040e0c030402060315040f020318060a060605040506070c09050c12010902091f0e1c05120903060117010603051b1306060203180102160b040608010b070c0909 75
    0x34040c94400694503030400f03501030181c00d002403c89003110310030010480189c0342c210030380e0780240000300a41da085d0002000a000340c10301d0f9100c00e501900c04803c00002c00d070142c070f11a400071020010b4034125200c0050b6031058603214040c58010640400003000142050000ac240e201c3c00384908103481074451076104140e600031307035106100d11030104064640b07044541141d401811321400031443c0c0521203000c9820381440d1089660301d40703000415000064001e101a1042d02d03001461211540000d0310b401000a00243c2c0642d0703984680c8007040320700701c21001141c1411500400130140c0b0380c602054146401c1c40700c03410380142e548034400000010010010403269412085942c541c0310030f08800d10061040ca65046143c00382480c408100e501d40220895a41c2c00038148000380080607040141d01e0149101110351401259800019015001101074000e540003960b40b078410741d80e6407841c1c4045002d0941c0151581d501c8500421603950523520481c10715100d80c0aa02500c0152200d85100d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 864644595 1250 864643345 864643363
    0xb1f053015091005010e040f0e0703201c0807080f04090b0f0301090b0106031a030703121b03050d0203040c05100903060e0102040e0c251a01050108060d1211 69
    0x1440d02981c103094814a4040d8a80e54030000e00c419440006140c00e000800b10f014158416006940e00c40b8201c070226000e4114281c070141040c100d48815680c0d2a1040c0400034041c003036044569102c43c1d8022614041d00000d90300d01c05080c64445500140d20b44e854107038402c04003140c210404020352456003540c00041c0000380103103a13001a0b0040710700288a4414103a0031520f1190349031044500008428801903030548081e45000180d4141e440b1701540e10a4604205962512400c0d000100b0000000262800c11180340c3d03503400c01d500001c3d10301d4520645584000c0c0821001d22280031103e01079800746034040c0c01151454070385503440b40440c07403254210f840300000564152040c0300f8080c0f07a000340003214048178001c524081c5081c3c091684072502030140c8070b9901002485220703c5040050030050f0100b06400c40707000c07854500e01444138003d0002c02070a16a0f82c0740000890f980101c400b01d11a1002070018245001156911851104260078950600000000070456a0320820900359 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 864645845 1250 864644595 864644611
    0x40204051806090d080109092a3b0709030f06090b0705030a0518070501050f12010609031230090b09010c09080c0a0509070201140a0b1f0530 62
    0x1404c03400003011800142c022602d03103402c2207030100c00150b0301c8202c0001103940c04503510440c540c100380c55841c0d848903841400034440c52490312440709500d50101d140c0d20b0100107240410501d0780e040d4180e0410449030714021840c1d000b010004a5512481d09658922448002607131104030355070303030b441814143c1e500d900260000c42000006000d40c03141c51340001a41601c840c000380401c001d42d0b551880c9001c0d10741001030204031301060316030f0030b000c4d1418000a40c000440d2503856250090016890b1302c016030b000141c4070702d07a03450503009159034014145020f000d95090340c0f940e03030040402c200801003911480d60f12042e180c0882d401401aa001e100c0034000499001c00c5030900406407160b54110040355003111000302c2a664440121904032001500c40349560703581c0c68016401024146071046131224198200701111909620025002200725421416603010580c00a40003855851070408210100302640911505903429a03038440f044200c94490b151504c844140360800b82d40100c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 864647095 1250 864645845 864645853
    0x1203021215030d0c051e0703060e01020c0d080f010302040914010c0305060109080105090a0212100507020a0c0905100306050a0b04090b010611121e0705031b011a060304020405180609 80
    0x1842500d820b004030103416600c0d10b420b03c4c004050351a601c5e180c031414801494600032900d0340644091080c00501c000710340112041102d203240f8142e4a0103544605440941801550032004034180500c803840e0190201201d0b0b85656800c0da800d02c401481d60403c00e458040ca000c403134000d441002d006071400c075507075560040381c5401c0c03030310001d00b2500903500b00c854280d050000300140c0302c0c0000784044415404031010f200c2000000b010303030b00b4910f5844114001a00384070070000703007540000c0c00d0030b81c451080e120200c0720707a82c4c1d600260807510142ea452840c50344000d81040411080d0300003d400200f40c1c50000340d500075401c0006d040b1804840c040f5401c88640004000094001c2403060380301403214050006201304112103001c0e0f100f16440045032040400d03146013649402010748038019400310449170349610003c4e1741100d035500241c4059040d82484503114001c1504141041402006410300b0709603240c0c0da003000060a8000c6c5171284164402c0000700103501c081205c540501102c8000e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 864648345 1250 864647095 864647131
    0x14040c0f080d020a0602070804080706020f06010e090a030e01020f1b09010509010608070f0e120307050105010f150525150509010504020a061b02060a0207080f0a08030412030212 78
    0x1424032410141d206860641240c89a00382054011500d00081544503000694411191400701468081e0740c01c20102c9100300036002c64150b80004d070917614060f405003160050b1780d8a80c0c0f02d42c6246001c84508a2903004800c0310780002c2d0240d40c0c10301d80c4a2050050b2054000c441411074500701c404051240e200000da140d103601800c100c0c1142e4050807050360418050760403c0c00140c10035402810075020000080c00c18103815103e01914005030b18001c0516401d0200041e9440e901c0c2c00c80303182916594038080000601a400c85240400c40d4032004061400c1e074403000c000c0e21640c00501c0d8450310506009010f12070000d40030140c084451190404082c214603a580250071500001d1003030005a142205105c00740c0da503403182d0b0013100c42c9841e02c40201c08801020800d9030381c002400a400030800702e00d103004680c0108101080d140381c44112601e500b55100c805544801c00c60001e0506801040810301181c00c2420052080380701c0d0901500d8410054a03107002000201c60013111004031b0a44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 864649595 1250 864648345 864648359
    0x10e060d060e400b0903131d1014040c11031908130b010e09010e120d0c0c0206030a0c02120703021011280c020d12020c270a14040c 58
    0x2d01c1c0c4806040c035460304010540c0c0c42c4201a03040f8803501414404040c0f000802c4007408000721120103240320352441140d0340e41c400440c2111100900440700720f0501c000940500146040c0e10100c0e055004692a004401c1e42030000411a0070340700c0c2c007000200440310540b03075030400003440040305002c29090200d9512400802815001d0590910170b0740c0b0280d45404500f041004905690108103112071580b02c242c03445006141d011803241181c01601e035401c1c00341540802401c540404400f082c06600101d08040718512614170000303600031010b0001c103002e42a0795114881d460010300403a24080c080d0041c0704600d400c07405044005900507504560b110f4140d00480d108010040715860400d119240c1202200c1c80c6031591011903841c419098020034492200e80065a030003400340c011141a0f4146000d07203040000e8900094421000c21811600f001c0f0b42c0043d007400441003103400031a11390506116004040e1618004a482d141c080030f0384024a00c420340107610420000e60712500d0080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 864650845 1250 864649595 864649651
    0x1701180b07110d0906120227100201090b0a021605070b07051c0c1202101104090e0d09061116060230090904060e0102040b0403140705010e060d060e 65
    0x2601000b03a0804441d020b81c0c030750001d50354816902641400d900c031080341d03001a002030080c4115051007016018002800001c4407590300b50201c170a881d02441002d0b41c242c1a826502041070040100c0c10003000140d48804e00e40c003501c1e60b006140d155581c00d0000d07440f00c0f840c20748250001000c2c21000580c00382084410040d0050090303d003404408409400207010b4900e900c9048050103049055006101640c800c0c0701141c001000741e9000c04c000c501c811303034211039a00a401615800e40c03030880c028a0308040064201440b003407c1c4e64502025082c030f42d040b40c0d003021000d8144001d2007005040d541403901e5003089005014940c4c000d01901c1d07040304040c0100c5038141c1070780c01e072149001c200341d5200c5510021903545180c2590101d040d61558649000140710340e111040301d551002c2004520f60005e08014000c50380074140325915007103040701583d2070f10202c2c4501804250611038511032414940c010b401c0ea05221200040c11a03a107100301c3c180e070306003149c01c00c1110460300302c413840840c0045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 864652095 1250 864650845 864650867
    0x7020324060f0108060613050406121419140f0a08070b13020a141201060803030105090c16030c02040e010c080619080c01200f150a0b0a1701180b07 65
    0x290020b0a400340074001a0000d480940b03081d02801e00010380c80c06520902141f4401041c014000f005255617a40201400c60400301041b5294004100780754250f0f00c000484420b101050310f000016211307282da03510400b42c900283c0031807601070f88140440000c028814114504e0050048030303598515441c0031181001c0043c2819400d0000c2c085031005a26000d0000e4151076400900d200300502d4080004c58450006542d9415582011000319100340c0202c0554100e030300545840c90541c1740c404100185004802d0300700d0303480c0200e00094012a10610741144960f002410000c2c200c28840c882c00d080d12040c801050104e442c50085c0480c506000f6207980c413500c03161001400080c14002d1160b05d816900081ca810041032141e038594807100c43c61543d1602245000b100d10803511288950b0710380c0c0004c000c60400b110f1a000040354401d1600078a104544000c0c9984042810004010558102642e20413203540d03071030107000310110461400b03113502802a00c1d43c400602c0d124000400c4140ca00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 864653345 1250 864652095 864652099
    0xb010e061201020c0d110109080c0d03050610050a0f050417210a020a1b0e070329220609020c0708010c0302042402010f05010b0702010201150b040306050c0702032406 73
    0x4100105a0340c42c0401d09181c5d1025500d068503885020b2400d440c0074201000c030140040c0000a410f545e440400200f002c0b42ea0001c0e02d061142c2d40e5440c08000b4250039130a41c140100e2401c01c4010005845103c3c06d1034207180340c0c141142001d441c0c00c0c2054613010501000c641d41d60180c4004081081c4040051040c0c0f5211011070341340c238046920003503e901043e000280807060f01107070162407013020484100031307040300700303580b0342600e0102d00050252141040003201508180d01d0108926000c14138642541c1c4041c000810350000416030149407803060368800c3c04a81c0e0f03a200440d29001a000400b04500904014072005040000303007400c40d1101d0f03845005061042004100d00b09008614460140c01d060890311050140c1e4010b0307000d410100c0d0401000b516080011031400a0440580b480300c1c001c1c3d0080003010807200001c5078246081c0a07201e120705040c0010800070762550004d40e800001c020200342490142e90201c1c3c6424100703407900c014003111040e1200c0141d004030748a0741c04001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 864654595 1250 864653345 864653347
    0x10e03010203071205271c0504030803040b06120709060e010e0f1b0f03012417060d020f03031911070501052502090c0904110c060c13030b010e06120102 67
    0x3c048009008031801c10800710001e52100b001172050410b0f512000d042128000d501254460202c0c1c41c103494840d082e00c0803070400b6020f042100f030340b0b100b10140c070152640008030718a1a10740361100000302100401a03540003c2c0c00324050001d410a02020380108496007001c80d2880c00d20503407082c035001c160414034043c3d0a0304100042562000d0842d600301e00f1541c040710545c498a008a0282d1080e040141c40341000000005107e4113000107182806d5241d410020045440c40c0d4220f9104044074950180b5102a1010504500e05945500c4056200420f200646d41803400820f0a40d040710300c603141d902c2c000f4140740c0c080340d400c020105c11045001014101c850304003000a003440c0151155101c0c00030180c04103c4141140304034003446160010310b4012146454502c3c40501e902408d02c250150b41000311002e480080a001d54000c60f84002c042d104998541c0c20582d0300c1d40000030410340000c3da5040c000082441c4640c6180039000c419098129403411005103d00f11440114030b448580c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 864655845 1250 864654595 864654601
    0x50a02191401051303060203060102190c090b0402190e1206010e0105030c01020307080a1d030316021e0f06030702031b0f011a09130501020c10020306120a080f03041b03030e010e03010203 82
    0x207030119141a0b942c400741c0148c40b502d821300102e103029100c0c02408541d0042035030b10400e1010304bc07502e208444511105111400e81401800281d00907400000e0300c0010b070410310703002540940a200c2c001e18001d460602c0304803c03245410f00e0840d080c1c2c041d6501c00380e03050041c4103904080c02014040303002030004500e0b04070f00d0f513140000c40c0f00f501084020000341d1000204885e03141402517168810060890703840f0741c0c1c0d00360644051b01d1114401c070b1044120b900e407611560191035216950340c0c002840b43c0c44400e205824400658802001481140410051401e040d13501e84882040060003000034560340c841e20880c5401c49440ca10326811140d460075414403035540e01d00c1499840340813040848417107000d520301580a0b0203609417903840c6000c0c54a44403104c0c2c40c552b000d148a06801c031084900100101407803a15060000000380103001e04200a4008403410401950000e01c100503900750340001e25004a01c030b0415030005ca0000d1980382841d4180c3d07070f00101c64602980c00b24003c514500b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 864657095 1250 864655845 864655867
    0x6060a0302030a120c020607030305100608100e040f060207031d0105041a07020a081c081602190302071521050f13060b1503010812070203060a09050a0219140105 71
    0xb0801d00c1d0002d0000c2d0700c04d089001c195105085810030f003940901400c0d15501d6603c1c010740071b05000c5070315503138038108450002550ba00c1030180038002c1c1d0000780c9182da020b0074900b511110190091098031246400520b510010b40148010072101c1c1c06540d6140700c10740c48004610281c40a00d4105040200c144030a001b80030302140032480104105c0021559035420f0300c082a802940c03580703d02950300528166030020344040380c10841c03821440d0307900d0340c50342e039811002003003001c0b029000c00042e400040c4801510f129000408880317030003401162846540d491061064580041300072000400003d42c50806030700400e03013112030007040c1c2010301c0145011340036a01a4803004000000003030300340c0303160000d218850380006030144004d482000c1040034401c00c002140c1c8207116402d168410118000c00003403110042d2844d140d401006420140c036803503400006010f003101d0031b8034140620100400141d84101900b192031680506400e1041e142210300d01c1400503081002d814801c0030886c0b14409 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 864658345 1250 864657095 864657103
    0xf0903041202030c09090309040c020f071e030c03080901030e150c03070c0c0b0c07060c0803130204061203110d11061602150a060509070302090f09060418110306060a030203 76
    0x99000d40c141d0010440301d5000292822941c019442e0300b008001040c0982402c0200041c1440c61081c0c50500200a207540c0c00c903511300946120764841d80150200b170000c0c0030208407413146e42007040d0700c0e00750b002c1c1c80391144900009990300440da020000200c41d0300550305809031020f4000410041d0000d0006800c0e502c0d00450010103424500c4000000034403118002c6602c01a99034108030703001c420648402d500401580810b03c8058644a030160000d0f645200e03110040365107500c85186800c64032221801c1c2c003001d40c2c28604a134480e41f9a0300c08107510400003030002205000341da415101a420321764090509038500c40c40020419584030304e52001c200003d0b402d40000708442d80d0070712480320580072820407000b40d000007400d85003601813129100040d0840e00580301f0840d84449a6100d2440940807441006034560700b08103080404030382841d04088a543c40b41c4040e0002c166841c03a00c844042403403842d01d0403940302c0004510407445040400406a2007001a180603c03141d06540000c0c3c0d403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 864659595 1250 864658345 864658349
    0xf1303030b060f04090b0f03010509030d0b0a03200a08031611030f2e15060c060b03071205011b1b0f0803130506060d080919030f050102120f090304 65
    0x505031100d01c45074460300c0b80380481e844480e180c4551a200c54440840c000613000c142d81d070030307c18044180747c0c82d007518041c4230f01806124410001e600c0c109020580e0030140404031221940200a0b40c80000852105e8032a00c1d110540f0b0600d094032808500304002c1960841d030400381540d8018000d140c0107010312071407850417540040c822913045000c071700004d01e01007030301c2e2880d004d80c006d03003055048614103006107400d180c0e4010142940c4d0002d440c500340c11034905420f400302011010404009076401401c82000803401614040344218400c40403a107441c21a6121014007810740c0c041900b80f040c203101d82c8810300e0811100d1010700c0f96645000b0101030800c0766080210381000c0800c0100416203a00c0f2001980c0103160f551a0302d0000e402e8045a5200b01047e5124001e00002402d28504142405540c584c0050300d18200000c030790600c0541e180e0072420056829940d403021001c41c51401c50030105038072910000d42e4070005201075203d0004043c0541c0602d941c003405000c0600804015242 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 864660845 1250 864659595 864659597
    0xa03050f090406030510020304030f0e01170a0905010e0304050a2702131203020606041b140a030b0a180606091206022b06090e0712060506030a021306030b0f1303 71
    0x92a01040c0000a006003442c1d0310091446c814010f1124005942c0e8000d035120300e0080c1c550000c82581400e09851301c0c070300692100e000034100312411030205141e034030250300520484000200b8601ea5504e16003100c0404c1c0702d8505681c0082020042407401c50359210140241160382a10040d000d03c01050f0719103000c1c0043d403041e401250741d00c1c104205613a0040284a842090121b90340795040181d05d40d1015030750715000d80c0c149503001030100c401456108042c84240c1d62601d45844501004000b90403d4480c1c2e000c0549459100305940d030b8200a00d4041d00125490b000c0c00000c8075a260105d40c507503407150040c090710000c1000740700f0843c080c4801150b009040503941c0c3e08403450914114901e4030455045203d004280840b41040764840001c2d103210901c100b042540801c4069581c2d403d501c5407111210740c0035254800513985401040d0008805411074034032550560025103205d0320a09095000d9980b08800c10600c107007400c003190440440e0001c1940340c20451030b22114000c113028050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 864662095 1250 864660845 864660847
    0x5090c1e0c0c06340b070f0e0a060203032401050d020f090409031101060b0f072a031a010f030c0501030510030c120b0a0b0108060108040c0803030c0307110a03050f 72
    0x240e144042031004004600e401401140d451414a681c02c504c0145120b8480003e66000455454902803019036000c490304038140c5129951884812580b02c10300003928410070030b05c00031481c0766448024038040a440984c02543d1245031007900e2500000104400682900c04900103910990300701c011203d92407001c08000d40c1da111050b0415800d4400c40f080325400034a051a00800d05034400d4003000307403480c0d4000a001176075a03030075503d0480c06610589280d1160410003e00010380840305021000e11102d86040b41c00e03010465400c04c2d040c16031081d5500c00740c0702c8a0f00320350602c603410b40340946900d1100c861802e02b140c0320101c4082090140505150f81c400114464550f001c0e0f9180040d0791003c1c03c024900e0312050110802201410215840d0f80c54202080e001009801040144017041e92042481d82ea10001180d0801001c0c000b9200d1268002c4003290380031050008500c81d400c21240c1340d603a402e000c14014942800c00002e00c00c103400c421001c0000070b07800740403200210f001c0d6500ca = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 864663345 1250 864662095 864662107
    0x10203060109030209180607030f0e0c060409020d0608060a1401080d080703050c0c0a030e031009330f02040e06030c0102070b0c030f04090605030c0910030209040f050f060105090c1e 80
    0x41d1681c41900286c143e01c2c030501c001c200d94030360305400030307080e610b416031040c814004180e65050783c7c0d031074090341150700030810302081c02914180d41c0a81203081c40310350007180166903510458103201c030a0301c0746500d26880d4060006030808201002c1d0050913000c000b01002104960700914070000500083c00b015240c1c0b000c0b0351b11014100503a8100714007001130f40e010302c61074540034020080042c072690103070140e00410319801c503181c0709031025a40c1280203242030100b000100b80c00c3c0c0001d038400c0450036040d00300d181040e034050310401c480f4030381c0f036100160380d181442140180080000c00051090703100010b820304590b4041130307000c1280c03540030189454600b9098854194003a16000010ba8000464001810b407440c2d0020341c1110f1080c0c0985440207443ca040c001100000c0383c5541d4403600b41c410810060401d050440c1d4401e001c0d00015020f94056a04c00b8201030b000040e1560680c4020014009803805442031600000b89901241c540f01070f51410b1201c001051528500301800800c003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 864664595 1250 864663345 864663361
    0x6070804090b1519090905150112151403011b0e0301050a02090d020f0a3b06100c030507020405040f03030b04020901202401090506040614060d0e0717010e010203060109030209 77
    0x20b44020f41507101b0140300b686062002c02140c0941c181009000840401c00c607504640e0a10584d021400b01103806c0d18030134108110146e0f81020741140300e40540d44c5840039030a000000c0a540010444d0303030359100c69040200201825074401400307811019104011580c020740d20075821156203581943c60002030410080050a041401d80c86200c4070321094808022642460105d1804c284a01003c2d0400c0b8220071341c403005003242200c00c107800030821040951481c1c010b200b030f541c0d814402c0c64114a001c0d40ca901040669034103480448200804c4841d0034101501401440e51000054804500b004807510008140c07c03204145690120112112020076203400c4c0400c08404500303507410071b007401540300c080c804100c00340706100748645400701103503103458540182802c40c0e000407040250304451401b008400c2e4095a8080450f607501d6400c03290304107003070041000620480345080f42d03946045544c10709481d0319800c0c5031400d07441003040206680c0c00800610940b90103890040e1180c1e81c06107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 864665845 1250 864664595 864664607
    0x11d040204090507120303060e010302062b0c050a171b0705031603020f061006021f020d15080d0c020a0b030c07060203040501090327150306030206070804090b1519 72
    0x40600240195140070601ea03401700b480d4900503110f40d03420054180d4410082100050a000c0294000410010504214064461040000490300c1500c2d4001e8001440354119100411600c011840210b031401056811041400300d1106011440c0818640140140d000c018503921085110002043e84000d000d000c005444040c448140410a400547c1c1806507482110828440581c854440015a660f608406e1841101d50980041c610b032140184200a002c200b20303d1212115424021807201d010507004820401021903003860b12136080c95481341c01c114801c811181400186800600140c9894114101302c0e0703648590140c032a12000007212030f5104044018111a001106001c00e2040c19030040395000d04c40e46900c171415443c3d612050240140c000030b0116039489500400c64a094121103e550290070b140006203d0744030390001c0d0880e040600180c0b204140070500703001d4884580300d45c1000c40310444200c000c44010310050350b034610611061040b20034041e0345040009010702 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 864667095 1250 864665845 864665861
    0xa0302040f1205010608070303050a080414100f0501050103061206050403021f0c09140303120c0906280516120e060f0913021602092502030705070509011d040204 71
    0x7100d03141d119075440ca641040168203030b6064406502c2c0070000070f40c902c07000451078220307941a2103280c18032040c1c00040d2030a42c4004c1c001d850321604800000c1883d201400028102100720b000080d42c040034010240444a05070011418145030050034860402c01081e803000c00c9030b00a40100da1039455180880c10400340280c114407945051065414955954110526401072541c40780f400903900d110090345032000d88a00e54041e0010050309401074090707079040f94840302120b8614a00241d1201241d02c5901180350030116074920403100c600d4039051083c01881081c54903000d411301e4240c40700b40c06008040c5030014481005000d2a8030303000e018030740119451030010601070b120000b1407423584042d800701e000d01e48540c4c401c1c4602e00801e0610300c00d076003004601807401c000c1160707281d00b0f0080c5000054512001030b41c42c004903e035001e01048115407242ca86501468072041180750a40c50418550051803107400410f00511801500c3c0c11103c025407260300c024105d03a00c46001140040c00700c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 864668345 1250 864667095 864667109
    0x3091c0c05010c0302040b16050a02100f030e06060916030e01020a121401081216050109030c1505042f03010c02030a120b090403200105090d080708090706050a030204 73
    0x200002a0205030065040c0e48410300a100911030520000001c83c100d106034010400c0a0b0320078001e0820080380c44140c0d40503244200101c03910406560005800c0e025038468500000f500e185009135041d0b890b0040c10032001180004129508180000806054000f00b900300d110025991003030440e846070f00814003400c8801c00865032a60007010007803800c4400720401c0039031814181614650030940c10700341d040390b00c00c0001c0d0a0070200756038442490342c4030032282c0e800b500c13181304003202044007803040e00c2046d07209845a09032300d219407914000301000501d0405841307203850700704008100080141c494558a1807419040741c0c0740c6641300e002c03103807480420700e426610340203130601c40680010007004d045017981c4441010340244007a0b4000d40f000100c43c40d4000113602c010400083c06461310403008007821203800114140c203803c031390031a80d0845601500d6400b10300d05209443d0071407107940c0c105402d803510090506c0c01051003603850b00607108100401030002a860003151017981680c01500e14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 864669595 1250 864668345 864668383
    0x10f14150301200c120301080106061403040c050f0102011d060109051b04030204110408150714040f09150315050a0b0a08190219090906060506120403030f06090f0c2010020309 77
    0x45d04e104e28022b09180c017410011402480309a0307e0320803224240c030b10039540300c01c10346055418201408115a48000c48505541d21210314004082903a14003584089641340107155961400c06c0c40029102c0207058800a41100c0b158800d820082004440542c3c4c4c06440110f001d00e4140e0100c0c03100d02c556400340100c0e009a46200c0d60340c802c0130104c2070140509540d45100d40e03030fa000c1c9200d054402e61041d07110304400c0d8402000410503079007003804401c11003914492140d5076a101c0700c400b040780b104440422591041003001080c028450080700150595078004130b82c0c14162055036400c0044100c144080107074075840219135440307101462a28100428840d12782d074540c074400242c0186801181c03030b9820801c01050764140142071381c85a103c0700000300c000b5116620305800400756500c00f00e10317070394640b84003081d003554900401a9940034402d00203621002118001c09001502c50301c0c2265103014420303e480084005680800b194410f00f0040c1c1d03d0b00c4407c122441c00c80201142c03c44486 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 864670845 1250 864669595 864669599
    0x50a051b031c02030f01061b0323120415090206070201120b120c0a050303071a04080706050c040512060c030c0c0a12080907082d010f14150301200c120301 68
    0x14654000e0750107070007005c0310300c4116602e41c40243d80740c7c20014114101c0f17100e044c0c82800403a2040c03040c6000e04a0000c0011011040400d00b03126907440041e03c0300c903000c170b16402d001c104907014072102d01e20346484008014009007a400152188180c0b40c000c1d0420a20003201810390940354440c0b0307012000107006c0d604201d100c0b0700e05900c4425041e182807041e0803820000a450501104076071f451907101442d14084031492641003014a8003600c1510608010300c1284006509403251500401d4513500c0340781c45a18000c100f0600703100c0441c101e00c00360811400c0c0854002e440081e80c0c0c109002c41141c94803101c80440940c9002d0790404042d000709001d0ba035022600e03800852240c00340f02d007035040e140c0042d1230701c20069a92107200c2d81401050040c01c000a038808146605d40c040b0f400070000414281c8148142d5401d881c03a507601110f405103d881400320344801c03030511300c074900c6081d00240051802c0e11071801204192900d00310441200041d030200c4588e00307100740311550321000c0354030707480356 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 864672095 1250 864670845 864670897
    0x2100f1e0e0c04090c060f02150408090a170706030b180414011b1d040e030d0b030c03010e0c040216050a29041214090301020c1c050a051b03 62
    0xa940c51245000780902c08803550541064050001c402d0b8010b4100da200a207445d03012101c0e410080d051404502541c4c0c0b00e070306101e02d500320715402507000720951a110100c02c02080210025603008080f10300000c01c1d100e80100700821701d182140c2060600088694a010100e02180620ba43c50340300304204104210410040d0840d2071490540f000003040019034001b42d841c22034041d680c058020800d400c1c401040b01c00d185550030700c05080644003180001d002030301985107810040344048110740310000121113040812030480203480c110002c3c0110100c0c2c0c4d01098841d4550580103008a0700000c81011100542d41c1011246501c84202c403400e565a040a42c5840c1c091003400c1c0ea80d40384450002000004150102d018a030001011010100c42200a60710719aa22072100010901400109a165001e20280c01c9058984010b4045840e04000280c8800309a000300300c1480010b20092400541c01070070368050500f0f08410381441e556070903120380b03580214800164100d0100140440d07103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 864673345 1250 864672095 864672101
    0x16052101030c0e01050a180b10020a031107150804020607020315011409100e060a03050f0c03210f13050907170a0c020d030b0a1a1b0c0102100f1e 64
    0x2a80550001021140c49001d0400303c00390a101c0c080d0312080c144001c0c8030894480c10f803561105951000015090383c04c0020444241104013801f0250304610102428035030040000c0c1e91903501c080c003804006003000442c114000e1220600010009203100140031510362030121080b00d81c00038121241e036600e201d0201c2901c13009002d41c0907841c104094091850501100c260f01403000250701d101c2090502000446084004150561040400320004080f4005004a01880342440050503801042c40185483d0603002402010b207400509007a518601486098070300320707101c00302056a5010b42298370f003100e8049821840d400700303004003400075154000c50003000e42c24450100c8a0141c3d00c6030380d510300303e07030001e01c0c00310140e0456803010324020b00c2039201c501d00c400c008004017101512011a80c008040c0b240310008046400a490741c0600c1e50103180103250084003000704035030441c0200003515010940d5440c6011621080380c4040070301fa0303410181552443c201c11880b810801c440c0f01000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 864674595 1250 864673345 864673349
    0xa050a0804080f0f0c090618010f140a030b060d290415020306030a021c05030f030a060f0b070201080c0405091302040c0e090f04020414040302061005100816052101 72
    0x51040114040c183d290200d102032000d5041e0001d05079129003c0c0030b010310140000c11b5030b60711845c5030b01016200c40d0b1250225028018211000b28078604204415410317003004d5146030b11502c00f01e8010000946d209220341c0c2d00c810203860007503405070189840106200749a00c1904900f280360090160f507029100168407480c000e503003805040c14203101c84000c80c8401d543d05601038110803940405401e2030960422064410180400c07259015183c0500b550411428082036130b90000c01e004d0349103010300074200034019200039144c4141c54800000c41d03a00c210007000381800700900018442d2a5020305943c020400500350b20751910b4280303568013404480d80000c030b108030701e041c1074000da40384a107a4800226102a16003240c0d0707240e510090071108001441280e11640b504203000e003801080ea030150040e031183e00101031500f41049041c100000c0b0b40c0100380a111600140280b8607030140c00e007a040a08460b0041c960010702030116040d00c11641c1d00c000c1c100301034810700c010310013076041a81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 864675845 1250 864674595 864674609
    0xd050a0818091006051e040f060e1206062404050d0b060a061103070618020607080d0c0219080723030c0606060403081e04050414160804020a06030e0a050a0804 70
    0x25443e901e0f070701c1d004a00e12407801490009442405000703070444581d411404403c0c00319505908042e40c40007000405a919005200000c0c0e1160300c02055081034041c1d0410b20784280060911440c1002c04507014901428082070104c500c3c0364900001080312003107030090180a0708520a41020782003070f009521040c0d81a50203500c42c0704002802c98800d24051082404043c0654500720943d16041c01600803540102c40d9920341510b001d006030703035020042070094858034a10340c8030b4500920400c100c80700f856a4809541103030088140e1908443c20036070f01d0306d40c0109036036200c200030700340082c040c19152000d10b448524145010766440c2c0c00400f8200e5182e4000032180700e583c03640c0a0003964051480010005c1005104030340180314000104400d484404078505c0c24103981d880003c041c2e81601190304801c01c018400c0c0104500040d00c00b42c0d0020907030602e0135950401d0b6010582135001486080105982d030a03a0307c808600502c2034804181d0047c0171613800380301c80d0030902c00d5503100d44141c030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 864677095 1250 864675845 864675859
    0xa350d200d1d0102340e060310020c010b0a14030706110703081b010c0509041815020a02010609110405090709030b04121b0b091009020d020d050a0818 66
    0x40318103000001c200101561665a2494400340005401000412071011a0640c028240003140c2024910640700300800e0700d18083c02130300304007203050301c5490b4290044004941807104001c010b450010700954510550100180d9032041446407500500d104030006a0000d00b40d800010f54161803820358500e0501141611020b80d070b688405e817218607a4107203011803504581e00c200040f849480c05082005004036520300704d8045080c2031070844401d81081d1000c14004106a01c55090900c94099122410f80007058140103603115104c03011010b43c42c0308a002e40000700180700c24400c0d0810b500401e942c0c0300c103100c481c0300b05410b441590880c0c060385010380c1403440042c0800f03109241884c100c0b07070001004800e83d03c03035442e0013540c04041400315007032105101464840800c90500c9001c02806106118401e05109036402d0600114a0560b0b60181c1062100009070b501d505400029580c100c607e03041650403403500313030309044c50361401034590000881c801d260b0b654440140103034450101d07054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 864678345 1250 864677095 864677147
    0x30a06050a0902120615091203040911090603190204050d08041403071a091f03020a09091e050a0603080304080a081f05010e0a1707140a350d 62
    0x110b800c0340248280c1400f4440d113500031401c503003400b41c0c4113042000701e4410146001c8540b40402d0075051100031002e035a44c07000404002d4055144203400d0a0144801084c0c604059200094000e000c050600e849120030400c01d02140d601540c1114010f08019040d4542a481d50070b004025402610a409034541c24406940c610f1134007003010300543d064405412410050320035140d01a4000705603042c1c00c241d005c0303614000c501da104441103907100107a40142c1c3e10980c6500c0102564500d0784060009070600c641d0050001e070001c28072006d003100c0800090b43c1e56481000343c4c09031035994400391180340000140001e126803040204140512920b031401d0944070b104665070480499100b4a980d0f0070b2469050004c3d40c1309003000313454504010b01c01c0b0601522006441c0c8e541c06035000c2d426056110038003c00a0b1001581800f40c0c5400c00c03940c00e005240b91018a03161500009904c40318000149140451b000310903181c200d610010318201c80954450520182000041a403241c1d41c1304c01d41051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 864679595 1250 864678345 864678359
    0x3230f061614160f0602090a0b072102030901230d06030212070b0301090504032c0a050f090a020c190620161412031f15090506030c0f030a06050a 64
    0x40b900c0c07101080b4100c0040150f20748945840d144c5030344084131006d07001c003c106403c1e900d0300030800c00790010341030103641c0c2c3c1442d20305240380c441003143c0031407051034085d0b880d0b100680100980b0301b11242803c05c0074410f441d1a050035100011001c3c01012a03d02181c0a40100440d501800507a442030320354003444680809038039610106403240400d0b003002040140000d90160308015000b500c01c0c200129014030840d030307050683d40121524002034800301c0035a9020318084400b000103210a4a070301c050801c01001041910070000c0c01c1071074080d00050102a60360f8200113901c0344001c0300b008180f5156075850304402a00600300800e00060720b155020b240b0042c4c80e4201c46030f00e4102e100540e000400d030f644900e9000190a40700c4803e024142c0c540700517000c03c2008500c501000e0801c20700c9035442e0140c4807458800313a0481d415404070030301c0e00141a5007008921007959022600c1544a60394141c6e019030521030a000c0d8104410080140002000039800c1030003660380888040c2c501d0b682700e43d2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 864680845 1250 864679595 864679597
    0x14061e1c060c17010612090209190b0402090d02060c070e18060604020313060504030302040b0c0f0f061003060b031c03050601020106050609010f0e0a080106030804060210050103230f061614 83
    0x30004003a90b000b40010000300d03006c0c803a10b80220054942c04140154150002a0209011206048001d00e1054500212003261141c0000c1340011601113003000140e502161240081440081c041d000000303c401000e90104903482c01030070526a000a140341c480d01c560310302c09054409003010310031440070440914050080d24481d5000314201c0f4005a05034840c4400742c030b00508150189a42080085050a0303c03c00a200c5200c54500402c1c0349840301d0310842c50700354400000c0020b50001004d00c5030602241d4468030884c1d0b0000b00101d0812074102c00207007042104030110220803c00d90040e070825805400a51042100b6002001456914000d001d081d1244100d02800200b4008441010601501c5d011040319409007400211a444401c01400c64207140c00648078800c0114007048490b60401c0650215110414184035651441e036030089130064903030808040c02c5406a204c4904407041064186501c40c80c3e04440c8281021369100702d03d1008000880000b5460030401c11174401520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 864682095 1250 864680845 864680867
    0xf0e010c020d0609060e0303130c05091b0d06080d0804140609120a03060909050105060a060923120607032301080c04050603031b070603050a14061e1c060c 68
    0x5441c90303110760702c141c3d2040c2c02000003000498200341e650240b80d045c024100003440c807400c254401a5003104040c280400c0303081e920b502051040f440c480401818104503010102015145030000ea02e5480d841c0c90800070302070b030340c115211030300c640410510b14651000302c1c5402a80074030882207035038070112420fa407070b040210340202096000c0020f0140c00c8111500800c046400c625002a200e0346901215054500c00c000945083e910380051191925121400b01e005168034284136098610713150800d400380b03141016682d20300c4002c00440f01c60b5115140e041500c0d054480596a441c90b0295000c0d00514041c80080890030039403ca40c261001070942e000e058584103001411280c1012081001a1600505c0950140020701c84003680080005003558a00c2d840000380c1800d07030030700d880281101d000404011041c1d04029114180b0000350541c9038100001360b07a0611205042c40f452a01c0052810240b40c20884c081c0881601c502d165030010b81e180e00c00c01041c86907640281040328180108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 864683345 1250 864682095 864682099
    0x210110a02100c050a050a06051006140906040902030a0606080717160203160302030901120c1b0c05030708010e06151827030c0d050a02070311031c0f0e010c02 70
    0xe24840c5000d8509448500c0c03400c51207180651109886aa44608141a07100115083e520100305d420800c911405a00e5011101108180c4014038040c4010104070180000942024000440040a4540c201210003a0003021825035803070401103d107000405040c8100030000c1c002c440410441c0b88501403c40e4003802000c0103425540701c0700700018640d0a05401c00013548001c11080900a000701791628456020360081d540390010030002400d00307548440010580741c40d1400f5a840702d6004625044800018800344a400c00e2903e001d0a503034480f0740125601d449014000108200c4c1508040410303840f42003a1b030541c0e2144000801a202d02040f42039000781d0304054282c2003007030040005d80c8110a940f00805a85009000c040003842032850480e691b04001b80b17107000c4002c1007081800c0f5251034546140b400070740d103000035101c649902000b00941c11403111185a1394007041002c00401d1508000c190081700b41c02d014010412800d68100455035100c1521307140c3d800782400158060f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 864684595 1250 864683345 864683353
    0x61107091e0f111c06080609070311150f030a1d070311150403080c1f06051f120f0e0312060a0f0302011d060d11030106090f0b19111603021011 63
    0x10848414907401355a0441c401c2940e520040004d00c0d607020030642e0f004180c0c0701c01610300c040c10b41c1807550341c60300d0415100380500c001c084092006000d2404440c40c28202030009526030b1541010b1101078507804021000300503c1104140c542c00c1d002c10303014110703442800c080040c00100e1040c010124500403440070b42c1801800100f022030003c3c0020400b822400d0103580c0c1600c66960740100c461004966407025584c1c1da042800746040a103404080e050350040f01903002d06d14a000101084030b114810792401d0307103600c5103000895958006080d01e00c0b000c020317261580401101c8035205007089030b01303d00c01e082c6d5030000104421250b4010702983e8060f9035240114540d03034070300780151405c03501207508048100f2024242101c103100e0002c0c10502c1c80c00c0c1503580d502d002c4c0028480c90041e08a210901640b280030001ca08172942119039803041c074818041c03407a01c80380094407c60307042c0200015500900041d01ea43e1840d00c1c61000540b88210307406003150b4a203a0040b641d030108800400c1741544 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 864685845 1250 864684595 864684607
    0x203161103091c060f02070308150d1101142d0a14030411030f1506010504051e0d1a160f020a02040f0b13020d1b0207061107091e0f11 59
    0x14030050000b064143c001d4810381c604203903070350074003100d50704016603c82a6012590300101580010a540c20a46000050002d40c100000180700d005840d440104005e42d81180c0710300b584d024804051103402420421070b2290028200120072006408203110141c40311035070105296125815150015140d541d0780c0c100e040d561094800d070b030344054400c7d542a4a00d1080014560303003040406907031030300000903020b00100b2140034815088003500341414000103210a12242d1908500281e00b10481c505840c4c0c400c000c007002c1051150303012005480054004040040b0042c0e19050034060005d0001400000d10f1004040700e030786600306480320042c1c1004180e03401502d00368024140401030300b04c000030038603805000914040108140e03143e4950700800c0c481d03402c4445201c3c4008048a207400307092025101340d80252900590f01521081c081d034071313081c10100402000000080c0c03c81030400c008c0b5104d002c400e0084001d18162a4501c0d07801d1103111a40c00101e0b000f00700b840445000d255003404d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 864687095 1250 864685845 864685849
    0xb070b070e04090f11040f110a0c0218091b0102060412030e0709060807050f18041704330315091e140115030203010302030a0210030902090406020316110309 69
    0xa808000903a12030b449070304a50104010819501d643c034443c03004c02d40003842030320500c0180e9607885010341046123000d43e00c1c003110601d4821100030486d6460401ca841c3d0451000522584004001d80981c9081e0703801c01100020001d02c460a80601c0e100c41c10522841600481e51744008450003001c0305a44003800c4050780c060f4110701c54540030f00040d03440e41074440005000704c512075031103050554841d010800260030500705040e0004829900052201a050301c07201402030082c000904e0203c01400f690002e042c0f8600341c42c0034080b1031000d000342101c003c5d0110801c100d414004c6400e0905c180a2900c01c0340039102c0c1100303143c2480308100702ca80c94450358900908a00c03a42e092180c0f007054007540f14461920851000000030021054694100381c1740003005001c49422006051040005001583c5c0000360324196550440301078020310800d1104a010346001b020003500560f203001400f04005064000c0c501c00c2c01301410700d1013204041d100c00c8a82c040c8c0748100b40629081005460114 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 864688345 1250 864687095 864687107
    0x2060f0c070b13050d0e0a050103020918070903080a121a010906050f0f130305010e0d140906040b0304030807030b15160c0e01090c032313060b0d06050a05010b070b07 73
    0x10403907801800b40206151581342c00d00212007100e01c0004c3c0307940d0980c01c0c50b15105021101612003031030304500740768903140805c035103054070f4280e0350300b542d0f28500007070100d40f0038040400a554070504541c0c8520708070b14050042248001869100d07414008401903040c810040c03c00d022030305964190b00145400b0003900c42d40e029250a9106903400c018030b05501c08a40003e002c0003180c001010b1449285007403050031103140d008160f40ca0703006500405103060b0300c007a8000461401c98031040e40c07080030b4070018405103d180d000e88000a40801008140b61b004850a40304600507102400010410b00030403540540101191550701c200b0301032005500d90f0b0b0441000300c0d62161100340141d58841c1d220010030403090b03204080090302c0b07816400b40181e00d130141c0e85840344080e040e5410b103040d00c0c501207058100200782c110340c03820140e80b1609004040d003041212410261021103c0d1a603820038101901f03080322108040c0e410140000386085801d0b0440b5a11500000f9048054503004011945 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 864689595 1250 864688345 864688351
    0x3060a0f0f240e0c030f06030c2211030108120d090b040b011a031512100617060f04021005130b0423010e060f0a0306030b1602060f0c070b 61
    0x148075911441e060081d00e503485011114450b008449a03111590850485101d00036081090081c5040f0240308454025409480c0c0041307604509280c56070754200444d10308121200342035800640b002d1061004503003129403070010305890300e05100140c1061500c0c06544020b00c101c0a9a60040d8507580c040250000508201c00440202140c501c0307041e20359604100040e64161b400f044450b0041088240380d02c0c1c402d881680704032134075003036140419103184a0b0f4003040f00c1c9802407020709008545080248140600c0f10645070080161980f5000156000c2c1c50b12040303c03041b403080d440407444881d8007440e15031007a03500801c80d9400382101786040300c0e250403000500c8480001d50030701140a90101001e03001070610180322081c610350103c030307c802c4151251449418020307018003c8031a500d805003255990000c08502d41e40d50350340ea0804500030300c141d61014260400180500510191501001c1940000d80d070882d480c42d1101840c40c110f2460035107209540003002c20036100001d03c4014400c0d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 864690845 1250 864689595 864689621
    0x604141c0912030c0c091e14040803060d0c08010c0e0603010803040b1b0a030c110d0f03081504060807090e031305130603050d03060503250b030c09152703060a 70
    0x2403682d44e0b81e6070340941034040380c2005404a0322005914900720440e5102c610040e4201d00c140006416011503d102000290010340034400010000b44680c4580d25043c0607283d101000e400b0542c0e480d0411f500812500100000140c80b030541c01d6400d2419800b136a05840c0c102c409180742c103241c6600e80d100c42c1d001803502e540083c82e0b09403480c0540ca00b0302603580721500a840b83d00204090b468000c014520710400640b00d14105096080414500500240555803604003071060b5121112504520000ac03021103034030074140700d00072614000c0031901c1e5045802200003840740c00b0078030b8085030322070040780c041c2c40c00340040304401c1050345451000324160702e4a8800000d800c6444e07844407424981e10460010205e5142c11007041305090803c0000700c0c010880d603000c1c10920200d058407804504a00c6441d00e460400b01c0442d4210310207038126001000001d000c01e61441d515000b8402c3c542010201c01000b5502490100d69850740f0703400e1045442006014000a9803800210402014080c0a100b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 864692095 1250 864690845 864690857
    0x11a090d061b090e0a051303081510090e0108060f04030309020a03080d021b0304050102030d0207050705030316030206010602031c020315041e0612050309210604141c091203 76
    0x700c154240180c50b02c25555a0740c1c10085040031250201c043d03000d4420340c0481e24002c100000d01c4031140702e000d030640d818501040c00703465450500c03100c40d403c03600480e44a81c100c1c0340b0994198000814400f160801b007461402c980e0fa0320403c94862900b280c20054802894001800292013a0700c96491144010800020700c4c0c0c40c0e0b151603038907410821019501e1175000400c0d40d100d002500b0022910074010005624107030500000070b441e8018842c080042640206040b8204001404420094940074007141e0f11034124203c0c1503804000541d0640c05405840000b2504034400700441d4400c01c42041513118070844441060001c1d440204654516140381c0300011599589000f40d2890302001038900c10720300001e04a8a04a40b4a07501086211841200003800204040261441143e0450700c040040700030040000c03200111a0143d01280242001c01041040803d00c84190300442c1c0101c411502201c00720071034260700e072070700302010400701d210401120128008a0a00520a113409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 864693345 1250 864692095 864692111
    0xd05120304240f0b0f010909021605011a011b11010c1b03140c0307030c030f0f060912031b140c0a05030c030403030201050c030f0c0f0f070c030b011a090d06 69
    0x4584000b0103201800d4100391035080b1a29080c24600a1112810085071845850343c1d4550010b030015032188103410a654000c604069101070145442040030f400c14002d011070658522003800100321103408070702256140303491107007070042d0300300551010764002100c280c0b2000c204019105051011400c6945003640d0000c3e131a68040d008000006510902454903040b0038a40c01d2703410310201d802d015019030b00c540000c00204031020140d1f0100c0350402c00190305611207080c05854000303d88030103400320b42410b0361441041130700c1c094420506035640e01004003622a503807140e01c0c904062010000201e0001c0300040c02d5038001c000b02080460a070485001000d203a40317072402c41d08144070525403500040b4042007410b03020700800c2d5101c0c1c00704402c203145203051500d03060b10301809486000349607808100781c00210416400c551030113130100c0480d42c0b2203989103480034000076540812a00007075810b0001134920032542c11400908910b01207a8205a1690180071114026050503500301b0b44071400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 864694595 1250 864693345 864693383
    0x1e130b0702040b030a05060105010f0219140c03070b0903160302011d04180609150203012916140f06060310090c030c2607141311270d05120304 63
    0x5c0350340d018440e102401056160030f0014207140c206440c0b000c199040341c140c002c445400096003e0f000c541c4003252043c03c0d420341200c1440d2040c43c601c00e03500b6205600000c50806030351000381c40c80441c03c9003154480c4035040f80640340006184802070120300c440440c0320100020b450b080101000c050000a89018407210000041c00e03012402c1d9503807607071a00000103201c00c5c0070580e4142010102d0951a551500c180320b20a40340006e180c0746118150408101710942074411141810202440701016203500d04017101820081c1051041d540324214000c100d200b000f14a0318401c0d00010081c2680441400e1200041c0507a076034103d0740e800702c4800c0800020f4503864010047d103005005039444880005190720b1045039580034017203d90003017900708565003c803904100425002e592100381081081200c0c400740c40c0d6100b200d500300d1004602c404103900007480880361000c0c0c060091914080780403c1c0111401c594802405039040012014108148074008541181c03190059850b500c0403080703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 864695845 1250 864694595 864694603
    0xb0d06050c0a09050f060a180510030c030f050403230412050703120215042a080d03110c0d0305071709070f06110601140616081e130b0702040b03 64
    0x180561045400302e000e0510960100c10302c4040c00d815031300544040c44030300c00a0020b004500190080180f0b9400103038500550030306420042001070848441c401c50348001901819034104005c002a242c030510f4056401280621805107400d500c50907400310401d0600010001c400700b4102d040c44041000042a0650140c0010709500640c080e003001811340c503002d00240d08a0001c00e046621191a15184080010a8a80143c1e0201c040c6410f41c403604603801e2405520070180c5041c1d075074150005a80b032004240c11132480120341c1d0420000c0d401c0c07000c16240780620007203008994004410b6011703481c041da020721380126079406c1c5603000b00721488244c101c10307100f00e48080791500020820071040c142000f0a5001e0300345400c0160030095202d5550b9552041440303558103002140c04142c8403a114201180c0907154801c45510445485041c80401da52110b10004614503411800111849840c1c09070f801e1440a0901d0401061518270310401c00d0308200300c1681c1c0199610801c52079503800300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 864697095 1250 864695845 864695851
    0xd1a0a141810050f180a020703030e0a03020105010306060501051815041e050a1706060108071101090503121602030715020d1805010c081b0d020409020c0f0708031204060b0d0605 78
    0x1500482d8401d0600050000c110051030b1064029030400b00030940350a124038031035910400c0c42800503141c00440c00e085002d00a03510401c840d900902815600703255064010320305a0f4002c040610056507150b00441d80c82c0314170120750b6442e6a418180c80980e24020300d500520a0079524011305080c5c6840d5142c52001e1640c500c003484801d0300c00b081107941404a0704400401700c04206800c425200c841c01760715158002c0c500c50401540e2400166014016500c00208502c444001c010f603d10910340709a890340140e5403428a800751340005050210410700c99118640243c0c080c60a000c01541c5840404040b0100824000c0d024000c8a0b60205144102c01c07581c603805107006065800d0b81456821110114880800c00c030541c0100001d821001280c5c0040803440602250b9a02044010200030b024039000500c861340009a00d0200500010301c08400c4541ca4082d160090f1360b0300700c2c680e928480d8680c0b501c07210352001e0008002c41c490703602c401024003016107000d00c0e00d41349607940011a6412 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 864698345 1250 864697095 864697111
    0x30d0c2a0b0a0806010305040305071103120c07030c05090108070315020f07060b13060b0405130b1e0102070e010320010e090c03010603180812061306030302030d1a0a1418 75
    0x803440c04450383d8405502c030b800400a080070840da0a0640700180385100d000c8010307001340c800c3e209000107518100020b09078000c105100e41d861704001d02d8100c0e25a8441c0c8001e03221050410000300e00d40c907080103c1030403200040024088180f640e80c4039440c407403101144092150b82440214413201804000303025951044400092154194041020b001100c214103001c0c00d10f4404140005280c0d5000c42d8192441210340b004a80a5911030402400030342c1075954110401c940c20302241000000414a902c0c0c1c00d1302a16500d64940d003c081420000344800f810100d03803500d1300c6a0aa4050a10320f102c000c0c10301d819441940f426002c6031010b4025182864602d80000040040d03650521440031050074a10b050795054081d41c84c0d081290180700340c0114a44403c0010031001e03518901500e40061206100f4001e203903613403d006e0340b0394110040c0180307801c3c1001c02e00d40050141a42c0f0000d90f9400500c0011124217080d0205408030060010a40010700d00e09100003044600042a109404d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 864699595 1250 864698345 864698347
    0x1360b010b0a0909021e09130e0307020a050909060a18050f0708070803180f060702150306030c0a230402040918060b04021e070f020607060905060105030d0c2a0b 71
    0x450a4010f200d44003036130000c44820703c1403080301148100c0d4407a600c084082160703003d80f1000d00100240800d03541740226104180741c145410440500800500740351802101c060b03400c103585505010405904480306035a0350000310020741c03a07090f00d60103d24422452000d0240c4502c2e03070750704c2d285001c1d40c8175403089640d80b14210030001107204001000141c0701141c055820300008552500d4000354410540340f0030180706031611030644501050382c41c213030b4004009144c2d03038149520b5109242d00580c0d83c94003c0c01007408151560500800c0801240e0340c550940100d00340341c0308103840001c0c110784000d500c0f0b9020040080d542d40c5900074000800321502d0300410b032180c01c4ca803400858442c4892180528014400f0440310b08140600da640146030340d50071592580b152820359032800d810080294414004a03c060900540364840d07e0041c1c4140112803040c0d81383d02c1010b0b96002c20800c103200058007008a9030004200106001d420340d012042080c0c0d178042c1036031005405103d608488200e101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 864700845 1250 864699595 864699607
    0x70f1704060f2a051927230a150c03110d0905030c0907080609070315030c170f1e010f060806062d1c060f02040f060201360b010b 57
    0x50321200b5000743c60450030002e02c0d08507860080312065201c058500240700e40c404041c600111501d420000d4100d04803609102540c0701c2400c40d41c4d88a00815071042081004440300860804611900c282c400c00b802e4154010300c0103004403800e0203140c01c00c81c1000b401141207049902d0811401480204580701c2d00407050804003854500040c102005201d43e80580c01e01c29601c0d0810045a007014095429640599030400140c000c0c20f424640c20340c1e03001e080c09001003031103481c01554040d5090101445000002900070565803035600003000300c2500a20952104100901452044a80040d002203041d00d080f28520307044415641c412000c0340c00804c10002c0529000c0c210002d10074001513500d10001c44a0302c0381200d091a00c1400d8010300c4005d92207009001001e41c0c00b07004580c00718041c042035075001801000b0750864880c5100310740c80a00041016401800b40c0404c0c108c0d8002036903c142140100b10881c9000c09060240c09802542208085039004420f40e02912840251540d529 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 864702095 1250 864700845 864700901
    0x90d05010506120105190e1c05120601050c0c0103050a0e010e1b09010303080705162a050d0305092803110a060306082d070305010e06070f1704060f 65
    0x1000e0340350f82c3d203076494001004542d0b0382c480c0b002240c00705204000116a107480c502c0b02e01e045c0050340142d043c59454998000702c01c3c2e02000400b1900e890500325a00380c0c691100555490180d04035403250f83e0084403101803e03500c6940220303406422448042521504190320b41d084400c000c2d0201000e0b08030215a50403a81d11050315012804240e03001612503240d5103004090960141c04841000030008510007160484c42101c1120340c1c11580b084a0038130000541c010901008015641d1465601d00c0040c241c60f20700f00c8120000d4050701d82d01e24200c081c01c00c00604d0380c1c8103441024220a94035080010860305007030f82003d50301c1807200c0d1402c20481c104000020040d9409042050f00301501070101e0034001c0f8030034410712441c3c60300c40700226a141c10520410000220045584a240c0c0000180308054102e43c01103201e9105a130100c0e203441304212844000c0401100229071800848002e4140301012203900500440c00092802d145400311400c0e243e002e455900f0311000721031204210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 864703345 1250 864702095 864702109
    0x4020f060c2802090106020d080711031e0409090b0a0b100f0e011e0c0b0c040501050403150b0301092102011a0d05150112031403010810050705090d05010506 69
    0x1421049400e1410600144510703039440d100720001c142e200085202600100e4500b0b101501059030040103001c10f507071100d4009645007619100c0b00f0020310014081406980030f403880c1000401e03014069450b12000101c0c0c222a240610300e6912004020000081c6100b034a00c0ac1c0d00c2d10034411603c50b005400c10b030700c0040584094000c40e0744035902c40c95901040c240c200c059590030351f0185c180321000164520058610301180f0b41d6131400005a6841e060b50681e1061041c074040b4410000b6110a071110904100c0901030390040380d020550402041c004540c3c1080c941090030302071a008150201414042403d540c1c40035411207150700b01d01112800700b505040e51001e02201c9200820000040c4403850488045804110380a02d481d450300106126092004862548034503241241551351417042c00c844030840d58050300001c5038424690f40182c200e104490495071200020640c002d40050f20b08001c100162000081c0b002c01c02c0244150f4032015070a000c0c5a0087c0c00024071864824144401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 864704595 1250 864703345 864703369
    0x10b1e040c26071206060207052704030302031b160b10080304080a20012001110f19080f0402061c05160201270b0601210507090f0303081605040b040305060402 70
    0x1919061031740a200c85580087c5800440e0301c1101c003003180a0742240c0381d0340b510480300c010017000c612803010441419050b400440c0500640340a000d000507403803403014042d005140c000101c1b01c55115110000ca4441d00105070803030f00300c0c3c2802000b1983c40c650145903512990020300c1030f0b0001c4141ca81403101000380c0782da8642c0585880e20240300e000e000200801403400074041d003c030050b840035000130825484401201a18000f0b6955204100034400310b0307400a0b1050f8000e04000d0703400071f8600c3e1013407404038011106a240b20402e0780740c5034200120307a0440c20108a1644419410200c003d099010b094051740d44c14100c55074031480e81c10300034296181240e00030840b00c01030403021101215405a601035513002054035039075854420048031141c070304e45900316660540c00d1904085280903402540905201d0b1103154903580d17201c0c00d001c07501c0c50038403018010400d004d000900444205002041400080c0341c0f2918094030307a001c41c02c0c1500a50810b40d2194009400c0004508000e9881e2038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 864705845 1250 864704595 864704627
    0x606050112230709080d030506120f030a030504020f090c190809031605070e0c0301080f0d0f0302180a0603091509020a0302060a0905060f0705010b1e040c2607 70
    0x880504101c6030080090403400280408542c0c0c000032101841500300e01c01400f80e031030943d80003515401004010788815550a44501340780004e00183c01d60001c1e00e0880001610003440c103003204000d0680041070000c0c821b076000011a400029542d840007441c9210341400c80c940c3d030316202411142500d210700145c6400600200d40280241e002000099405036000808048411b801920301310b801c1007207960204000f84c8807042809003100300322000d141619410411218a165283c0045c0ea40d0381c00100c11402041c80100c09110f01c80c400d400805040000c0004541e41c200000c002c110082003c0e030100001a40d610000010064642403100c0c00c609165003d03c50a4100e40004045040600c40280704d800f00081448200780500c039048002c0000900554594583c8006c0000340c0d40402e8041b12203501c0c0032000c141c0740c50021083c01d0155000741d40003280360102d40512000308003100104062107020404902d80038848008180c40c10f402a0284d07a07035084c0b82170003404958081d41c1240f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 864707095 1250 864705845 864705851
    0xc0206040c12060e1002031b07020603070503090109170a03060807030210050c070b04031b0621020f0c030f1b030301060507060b0105220e070528051201030606050112 73
    0x1000c00d245221541c15a40c41d5100d01c1c00251440c50000c00030106070b4510019809020f40c0300740c1003001030340a14401c00e400350300c101d0311170b03016000d642062140038002540650140041103c05101d940515480b0030b0714070002906461588032000c42d020191390081445100143c82c000b425410301507000240020b4000305000e07400c40d40080c0f165039041d0045003c00c80003180c0c0001600e01000910001d160401039113680d40e48070b003040c00003505242c4100804419003240017a429126030f25040704135004140c3c81b0328903140c3c811110b02950086011103140e045c00d006094034601e044c8000c00c46c0f09140c400183d910301d2a0b00d501c0b651400640440315030740d003044c001084810f402104031074609a021100107203210701c080045c0d0b298000c10822800c41d8400043e5109000950203100c400e699085140704e89680d9201d0080301d1a118407a6600200c1c0d1580700a0741301204071001070b005981a030704000381440809040781b650a0303000d0f4000d554041d11402c0401055070040c0c07040081c0c8403444028 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 864708345 1250 864707095 864707101
    0x10306180f0609020a030f05031216080a0e07050a09020c0606010e0904030f0c08191815030b030a020402030f01142b02010905090106021e03070b0c1602030601030b04060c0206 77
    0x80c0c50400241e4002418107074541c40000119a030710343c152030245174442c8180b600307918181002c964942211000707505081e402c5001c15100e0f4002380c042c0c03004403829611a0403a50300c07004000041c080703049150105100300074000c5099604c40b00d240c00a49035489005890740195800d50f4034008014065074140010b641c00741d00181c80e41c0c40403aa00c513805003021091a013001c0c20440d00e4014818001d8010640890740c441c21001608101d44a0040c40e03441c1e400402032044101c511079618483ea82080b13094054005189001e9046107031031707800003403e94180c072a103038000ca0141d078803c40b144403003102c409006010303000c0f00c64007043c00c022050301e4408014412a41c80344203562083c0c070b0100c0d18950980300e40c046a105804d0f640281001030412140d0703580d61070300a5614040341504d04190049007402c110131850000c1034803c1c0741d07040100d0025640312405002955449040998040103017414010f0168070204181c40c0258030508005089140c04d00380f0308200ca4010291004640101044c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 864709595 1250 864708345 864708353
    0xe15011d0603130503250302010e010c2001110409091e2607150605030111031306020a02161805180601050f12300f04150c02041401030618 61
    0x98030703800126401c0c0400c540a036801d2040c1745000300241c030200c120424100f280115142a107038618244030390028064440d01c1c40d0070601340c0f0440070100c000190041d0802e13451211102c0500708850b05180000303202c00d070000c0042ca0903413050300295886a100c00303068081100041070045c0180075071207034048544850f51403116504580342044040c00c0c040c401d01448031104000c540c6803d5004804801c108003e03404103019120500c50a03101e03500c1d16220403100c81c0141d013120b00c03540d100000420f00340001d94451000350480b20901c0118860100081d20802d005a019406411135185240c40304004d00010815140020800d1072552050340d11800240e01c002030391030544a0469454844d10500f0700410003108c000140700249104450054088110030b000e06101048003104843c081e103500e82d1800282e02c1101a03000143e50108420481c5942d0280722081110003480d104d0409a0a03030005019140015907003e000b2080100410400121380303c1e4201c078000509011760f24001c0d0f526 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 864710845 1250 864709595 864709597
    0x60906090803030c0d0e06041b06051e03070c0f0507030c050f01171b04030f0605010501030c1715060d14070201200d02120903041a04050f1003060e15011d06 69
    0x144c601c1c1080100c2e041841c440aa08042c25001384002202c0d920b25150405880840c440103140f009490395010101d8550b1003101101c92540f400004428034100c1041110110341c002416041000080e411200000c0c2440502c031100070f0180e401000c5540c01d508180300c0c14401c0d54000c81c41180307050341814481e60030541113542400c2c0c08118030701d079031703910550b080038101c2d1540140c100180000340401045110502c0070207960084104001c10b0782c9400c010b404489150310504082581180123401e1409454051544140c40c241607680c00201f50000c14019004424000051034490190701e5513031700c41c103162503031023140780c4024411082c42e0310030010a9031040c80444100c0c2c0001074071603015521a0122049145228941d10701407505001c3e50341c49400c01e02842000120048054504d4500c8205680139104000c11400384815601d0821140038501e880d04800d0503116400014612407040314940702e030800c00510600d51000c1c0000500e1001c4d4200a0300e04a6803030320302200243c580c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 864712095 1250 864710845 864710851
    0x6031806091e06130b04110307080f06090601060c0209040c05030d0504060809060f0a1820090a0603080405061b07091a150f0702010c17040905010b180f0f040603080406090609080303 80
    0x444012a44c1c2c5480c02c080d000e031f0b03a036504c00076090b102c0c40d003001549003c0050349104008081e41542c0158130f804080645510003885810001224084d00401501d0566042030b00103101d214050380d01c40d615400700c0d00f800444442140442c0b000300e4100312868028812681c40300c0b0701d501410461030010240308001034068107030b5030019954020180301b014800170b01c2c002c0d2a003221144c544084101200078004110b1150b03140148035640c0400c4580301203004440030740b54405000b81c102070070070052101a422031000b51500d130f07806446400100344140541d1024024011012450008101e110280c00d1588462180141e40469130498120300c40025203030320031001200c03a680d9100500040f074010306143c0000e00540390114210710401e01100007803044030030490b018050351782d07540c03904a110701030042000d12203080c4030300e01541440c1c644204010310074000d28041ca80450203000c201120380d0f94108690031000024141f011540003000f000050800d85000300c4940d04114800d0703103a01000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 864713345 1250 864712095 864712103
    0x212071b12090302090c0417030f040506030a0603020603041a0714041a070206040e0f06060c0307170f07060905100501210c0b0c1c1b0206031806091e0613 68
    0x4041c91803540b0a005150003550020500c107005d0405800041807a072252080e00d448401145d1440c294042c0801980e0285119400c11802d240c585001c1c4016642b000b40801c0460b80e42d00f4001c80181da51001a500030740c0140c448130032900e0480c10704032440401074400f40c2400380c901c141e183c01d80d00c041c00b1030303007134800f00114141d0585c003181c8090424003541100030b502400100340450040e0384e11020700d2140324001c1c11a81d003900d455041c44905e1240c0d01030114141c104001043c085426103881420824144034038500e803080102504810790048803086400c55100c0d06c9041c2448010400f01440038a03542c820082c5500d403034203140d0707100e0340324450800d001c0c0c0e90300c02c4405001d80380040d0030050100103140341c4d031412003400380c0303848101d162011402404d1102c0c40b04001c074881e020f154011125074000300c1c4035040d542c0030031606030030003800d59440c00580384520062410a01c8103602582c840c83c01002d07000001c0803c983c04409240742000d40d54000010800c10b00c000459410420b500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 864714595 1250 864713345 864713363
    0x606180302120f0609151501050f130302030d0e180f01030b151f110d08130f02031203040212010207080904090201032d060609300606090212071b 64
    0x910b12441c18215128286100b81c00b54400b0009003090200f1401e035038040c20305080d00980d4a40341d00800070204079640e01d00151007030040f0481031601c40e0003030080c801048124016156a43d000910302038051411000092039400c2c0390311103092407000c0500c6608a00c90340e888910b450304c1001c942d100705200141c9200055400b181c51311140c07145040c507284003e0b0560ba1128107442c0e07115401c0040c444583c002403c08a44840c0030f01c4d021560b00030014090303031000e030b854880c0306051101d03100c0750f81b05451007000c41c1c202c100107130703010490b21451081282050740c4034549401040a9000d007039500c07100503401009a40e00051901d41103448006040f14001600f0b900c0e800100d00900042801120740d842c205d4814940d411030801e992080000e590007800501d0320f685080300c8132501c612031080658004140c00445d0352405a414400c0000c4007414040751400303490724002e40e070b001d07405600050350004e4100c084010f040423055205115051086200300440040014103081c04000b07840800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 864715845 1250 864714595 864714619
    0xc020f03040821160605040201140304030f030e03041d060109080706050415110f0109021c02181e0f01050a060309030e0f04110c0102180409020a1a1902100606180302 73
    0x30f0a40141d441d81204036440c02c04054040c5041802000e00f0b5030283d0100d044010303560400d0740e120045900c06c51b0305503242502c401340c01006401a044407428105180024400070a1001c0110110980070f406079030358003100d081c24400500246901c0d04503100d01c0d04080d40c107000305a0010f04842c201c071130b001c140c010081d10200301102c8148038102c5801c00341c0181241c08111950541000f2903c5000f11100c0240108410110301001c80342c0e40c000b90132070114003004024280814403190720603440752035017001c000104e81c50b44410038200d039000e003204109401844203041c0781d21000050300e15400c041000c4601034078094251075000c8541032240e68403020980480d103071900041020604804c2c0c0c40e807a0f0081001c054042e400407100818080c2d02050082c11a242c40d0060015164000d004488140d080c040c10085580140e482c41d080581c0c10414800140c031032880011031070826a001d000c01d50701c031055076402daa501e540070200f04210201c190030104d041460080032603a040356800b030110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 864717095 1250 864715845 864715903
    0x1f0e0604030206041502060a0e0a020d0609020306040507030c06170f06010201140c1c020406080c070515132003060109091506120212060103110d03210c020f030408 72
    0x200c11500025000340d0007041c00074514400e05c002e00e0303510349140c0951340c0a5a030910100112a0112540c40341c0c0e6120a8607000503043c4280c0e60759070540a900f01058150039078001c41d181c40801c0c1e0b001c582c01c0d480007008109006001c034480f0090022031401d06552a0b6131841c00300c42d00001b4043c440064540f44c0841c42c40c2e0b00075803081c41c00d0b044107591640c552034801d1030880c4580000038a01051101c01c1d07849500e0701071501c221810348000d916112110784400c0b80803a07158000309811501441020f000421440b1701081c0c0c40e10a0111007407804040c04103150060b010f00c0c0408070640070846001c02c01e1155500410514107503003c4e1103000030741c480c0a0900741c4200110340d4807609114138040000c2a50501d5443c420602802a82c41d070644084405105580d000240b0010700803510a080400c2e05181ca419421603941c001e1611401018070300300f161104560550445010329035411869100740e405100500e00d811008001d1410a032034402c140f0b072140c40100040c0b00c2c0407822110b00003e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 864718345 1250 864717095 864717097
    0x2060a29060c06040302100f1b03180c08062d060105031f180e0601081b0f040c0c050d020f1009061b020a02040b100e0f04060b07060212061f0e06 64
    0x202c58602c0454040c0e0a060130081c0d00c0f840300369180c0007502c0c14102460b10a40c41405000718640c134013407522200043c28082100100007404e00c880d500e40a41159501090341c145a00000d01710381c0300a00198100b0743c4c5441e0a230003081070800d00303407031030303180d00091a80f42c3d4003410341d000c1402e091056403036840110380c0035204607440b107070040e450310007601040c1c81c044400254003040c5240d10410400c0143c08495664250921921810740d10207105040c44616001c004012440c001e080824403024070400241542c82e0450078100082100c404441400700804c44041b8212550000d003280806902c0b00c40c1d1a1482c0c110401c80301c41e100c1d61320034104040c0344c2c0100980c3ca10b140344074181d00301004000707450300d0345000141d208500300f144100030b520b8525151000e90000d615000154000e44080c00505a000301d40c050f4041d944000c00507140c001103000b27040e481d02c24000144d403149041039400f203050020707126038040c5120203011178000c0c0c401c40754030100d10000e080100103010001c00080c03a03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 864719595 1250 864718345 864718357
    0x80402011b1a0903131a09061c1a1e060403060e03030a05010801020a08010303210f0f050a090816050a020a090207120f05090f060706020c060702060a2906 68
    0x801551540c5a40c10700030700c00e15102c041600b490451042c0e40300c030b076207003680c130300a000c41040d8009440344100200940d04c103100b2415407446290b281040e810600245040d004403103074203c440c54119010201d1007585c031400e6a4500d01d5461200b170704204d207010409484507118030510360484981401c0d502e64928040c5c5004560000060201110f691600343d00c0b81c0080d2007600ba01030821002240880f130600958440005e02d0342d42035802da00e1034600325a41d80c0040707106080b40400e03d8a004038101c0e140101008203840780d101194100300007180742c00f01c0d0401403040300344d10b10b411001000221940120760105330030800454170040c0a04119003402e91441d002584001440d500003810340040d0040d000c0305026625400300c1c840e0341e04041d0b0b040780e800c0c01108000390040100000920340140c0301103514002518060810503d541c0382c004a90010442140c0c0c1d510a40400c0201507042003003d078842c80000b024070502c90803802c1c03840704040c907070440c1c2035503644480400304a484407819111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 864720845 1250 864719595 864719627
    0x2010f1a040b0d020a260703020108190f050a0c0f170103020f1c0605040c090509060c0c191505010503070e010e220318060e03060412020106080a0b060a050a05030d08040201 76
    0x10120341c0e121010740840944901925410f02106c010810080d00820308008a03901038494074019501c1c04041c0c1680b10002001c0c0e00002c1d81c951156000c02aa40300d42c0e03100b022030f0603000449004424003d012240415198010002400c40e150724219402020754116541a103a5a03820f0f00000c00184c03201e15460340420b2070040808910003403200c5900181d0156016403410014140c40e00316080c144ca40460303208040741e01800c0401d64007050480100604651003060741d0005490407802c2c41c0c5035501e400155440001c01003002440041c0388200c81c010142117004000c010f20700b50b40c0103002501442040414560700c0c002641c0070301c2d10040c28003a40f040ba8500c04804001f0318001d40100d003030684000f544e051029000c148640102c012100351007008004191965660f035403030300780c0b00800d44168115501e4100000d035030f0341d04020005e0108c2c42820b2003400d500d854418002d0700d54040d40001d10440300b485c0e04112686011941c444040401d1418140c0707907903a40010b0f243c03d040c02280e03003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 864722095 1250 864720845 864720859
    0x5030d1d0409080316081303050910051e0403060515101101020f0a0315060201060617090111160b060a1208030a060e01140a0e1e150a140102010f1a040b0d02 69
    0x1c02034201256046180da000c5441d1b91901e622500260f0712400e516850007404038004110840d4940b4044010700c0c241c01c45403404a1078000d40304105400349c92100242c460f004c0010405108000040c0a1182e100700600d08400d465501725000032007900c80f81e10100148803041135610740d885c03401e4040b20f290100b021601d954170049400000e004085003000300e80d0b003a83c410b4010171864818094201100d1443d0b5032140c500445008001c103644020b000c01c1c20a40da07d01030a004041c0e0700002e025450b00c55616441d0b001e145040c44085540010001445881055400e000040280c0a00b070b00b429080004a83c072592400c481c41c1c020152500300000003540707180001814000741c0302d00300700118185d400e920b445548500040d03051000303449010b440c0140012202080b0702d011502a402400c40708841004810580440c940581c44e8108214034007151188030740c0303540c0900800181c3c004130321080014160110407a40200710007003502d44690780303034400b00d41e1a64a040d40d15010a40061483c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 864723345 1250 864722095 864722101
    0x61e03010f15020c030d030f140106111605030a06091410021305060424051603021b0315040b15040f0e16030804120609060c02010e0705030d1d04090803 67
    0x440100440d8803800740341c06900b41c040000680b010925000c2031102400501010001e00019000f0300802030303948220720f940313400300d0308441ca150402c24000e100e02c0c1c403960301201d81e1280702400c00314070804403000301180c25010009078a0010340788001c04d030040b4000800d0700d12441e0020001522400700c404031301c500c410080440d041540100a8581400b00c0242c40903500d006104190241c6d01c40c2c1080181e491045200107800321180c0781d0441114a0b00034906170381100304d00402d6081074402d42c016400a0003035254180031000329840d035181140181040c0c00c01080c81c02c1243e2b00108001c00b001c12040c00704a1507003c440300c1180b1020010810702c080502c1c5040c00d80200306019449015104402050641070780b58220001a02d4000709090326041c10800b01a542c64840030084403031355034802c0c50380086041361203040d003180069400403403089505141c081c42c1400301c2d04100c2c440d42004004c0c0c0e01c45500f0003200306801c80c0c0910a845c0100070000024001c010300380021749004000010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 864724595 1250 864723345 864723359
    0x211b0d1404211706190515091c080a0c02010341040503041a0912010c032a200109080d0f060b16170a02010c0305060f010905061e0301 59
    0x211803071920a00c0c1501c00030407201101d0405440050001c2d0050f01c00101e03000f410004074519481074001e07100303030005507034002040c02e01002822a10310850007165403121840d103d245100700b01012039006040b2266525105183e20500b840c400a203c0c500c0341d80b80459010b40c0148040e503d00c12841c1c00c0c0c1600038004400d01d81c2c1002403150000d4000c29806e8003440b2100c610501454100c8001c42c20507080581c29a000d01440c542d07441c030100c0c24424a0065074401060032500b4000600105801082e00c0f03000d81600c901020f070444000031802c9009000034042030800d00051945030011062a042c0010340d40468407000d43d000650900c4103a13418001c00c18001c1890020000003000704580c10002030003201c556020300d0803100d80030001032540440116218019601440d07030840c1c1b40d00c1e10081030b11264095000c40015035110769007600d10360b4051260650020b8103403040158603240200003059100680669071180c040401c804104107944070720816118200742055950396156a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 864725845 1250 864724595 864724613
    0x50105032212030f0b1906050a020313121509150c0909090501020403021f02060f0919110a060509030c060a023a0314060609010c06090602211b0d1404 66
    0x4c0c0c0210041c244400500b250400248601d2061102024900c0b240c0c1000c5d01200c9a601c10b485110842c4403d12003800e540b00e0144511000748060020315503006d040303280104040203080c003d0046240307410021400300741181750320700c0c180106000c00110301e004020140d6030f064071904051409450880380c201085815402441030368001c0781c040810401b0007848058010425840000603000600490b81c0c0400341900d0341d80011050050fa00350090100903110900d0380e030813040e80e81a01c040310021035804c0458925010700400e160292400c911140420382e02c540065210f4080c0400042c2d40901c184284850242c400032001c1404200079030324a0000100c0030303401c4100d41003c005000d81c440600920908081c1c4800c6101d41c0d106036220800c000b25034120924450501c0444400c1000040c410304c41c1c0702d040c40c860480141c490407485da01d140c080d00410342c014440d070002d01c02c1c40903102c4040030484c41b00103080b200f156038420440480c0058841142900c1c141c010402c144001c1001760744d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 864727095 1250 864725845 864725861
    0xf010326040f36020a0e0913060609020c0c09070905090103051b010507120815040c1106060a030201091206060f0b0d0506010801060e121e03031f05010503221203 71
    0x4aa980c4808140c0150841c1c03c4510b041c84401c5400b085801101040950050f00d4a400241807041c3c1180b0b100b80452a814011501c8020740414110302100708100e038800c40c4098032a03411f045040c8a0f4840e0081d917900f25100f14240300d25241000500c01c01c5c841c1031508054840136007003203400c0d6901d20b012541c031101000c000c120403c2c03180610800d035200328107643c480c50704251a800c3e080c010050540700c0010240241306101c2c018035800342e030740d00c0714050006c0c1012195207080041d80301800d01d80c10503001400c282d1140501e058100b0260ba0300c041c2c84007c0d11100384040e8240600c42c64500020700c1594404110241120360000311b20301d1480191500c006101018015a9505001191034a809010b402c0120701c407212111914100800300c2d6501c65070303007800c07200003480b003030642c400415800b210f40b03119600c00400c01900c0d0340c50100c020700c460552503201070038500705000a00f02d800f0040031b803c10010b0103200c03421a0154020788240301a0020719150025000701c03001000341c0104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 864728345 1250 864727095 864727109
    0x4061b0f0906030b090a051017070302150309150c0c0109060f0b0901230f130507091a0a080405100905070603110408030301121b060e13050f010326040f 67
    0x4501c1c00180d072402030007805041e14005020380c12130b655400c00e010007444042d0800400200d00440818050b86000010780c08401c1c0c42c0c001d00c80c2500d184100507201d160104084540941441400311551001505d00c0c521103102c00d40d6011992a0341c400002c90045911480c407660038000c101c000d002040d4003480600e9407540e401d00c45440040e0502c10800402c0c4034040c8500c001e801158102c4000041034101064001c150042035103628001400300504500802e448641e1101402510b42d0040d442d40c0062800300340c00024411141c8101100b070080c42102810f202c4d4400004003045130500090100c0903264070f04000c0c0502900300b256451001e809154080791030310130540c0840c80c401d0190750444c0e0f1080c005618682c00d00e0541c080c6135142076400c480400c4c080220101105800c00c180014095030340c1d403104011511402c00c8000744420364041c0c4038500d04024044401c00300341405055a030000960409140720700d0b80e401401c3d114a40341d07089160080b8000c03880000340f801c241c04903420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 864729595 1250 864728345 864728357
    0x2012a060b041802040b13050a1a0d0f0b06010c0803040b19060f1e0b0301081b0d0317180d05041706011214070f080a12020c010e040504061b0f 63
    0xc0c4810310045078250f2141454482c5400d40c00310041c0780c5034115241039400900300d0f00d03d0301e22000081056820648401400303035202ca810589081d00320b01c05401003c01100c10fa012106640c079480d83c0c8940040000d0015201c2c1c00020b045640642c5401c10b43ea680315001503900d01e02810442c02c0400150340b0342c0e000c2d4100d002e06441c0c0d401540031300815074060300811880140740440d00f480b501d110740f4180340710380c150800c0003552403110000740d402001001c001d8003c500441895805400c203214a0b5031260b04030039142804654000a00310000341060401449612640080b025183c0d166030303243d0310391180c10220780c0481d500034098001c0b202944104055200c0d5440c20720b41f00c810034010003001d0350b884000301d000700c1c80d120301c00108130302d02c02c05851a66403119a203008911990b002040c06034400c101440c00c1001c6403c04c500780010030b1000d0204481000c0009100e000805d4000d413082d901c40d0b0110b030903c403040d40b02e9502417049032140d00900c0100440030742000304200c0e154011640c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 864730845 1250 864729595 864729611
    0x150b0d0e01110408030d0209040612030c030305220f03021203010f1d0403211808091801050a230307060906170601090512030c0703260c030306090402012a06 69
    0x2c0420981d02919010030286041140c4c0e01d003690001d410003441c0c0c2da40661190b1000a400802045004000c0e009645044401005043c0a0180c440150a401e1507109482c0190041000301d8802004c0560000742c45000c1c1d034180c00d0880c030345040100c414030140c600000000c0c00400008202085808991200402117004090501c2d41001294060089406d100f9101917040d44403200c810f102080b5240003c4403100000c502d46810b50356035088800c1c80300018200300070f160401640c00b518031001020b40040d81080d010030703070001c41c5102e0388200c00500d8102d04c2202517110344200301d0710303030260231a4105a502c50000f001c0080c0f40c4a0840811034000388011203e4185004a10580381038440080d042d02d0402804180404400c051160780000d101e552400b00c000d12042c00110b005115210600300b8808954490950b03114860456040801008101c0100071055030b501c0b940032100c8440b10317900ca00050358801c00c01280c55840000c5412500e000003000840c0b016800e0151030300300310042c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 864732095 1250 864730845 864730871
    0x60e10050706140f06012a020907090308220503011b050f1608030402010e180408070804080118020f03010204271103010905070210111210180605030615060d150b0d0e01 74
    0x1f07194080c51000c810f10b0142c0c40054107000c03240a402516070328100e915540d5984401c00709400440e103c2401c0000a02d036805504040030340e000151404a00030414040400990350a000003648148107120300030402c00c2860801105540141226164044840b413035482e00c4a4180d2003150128085801078100342140d0500c182010380348200b6240c0280c40ba220341c0ca82c0c2100da04140d02c02c8608103000c01003c500341c6420700500c3c1d90818140e035511103119452040289105011280300d00980c070602040000410039030b6004188100c3c2c080f84070703078800c0c00c00840e4082d01071080e5004061b82c00100000321850b0627484581304c1c03a0140e080d1285045a031b42d070402039410342c5c481d0204126041c02050100ca5070055010340000c403900346484c009a98a003403a0130495201451564a603407040100300504003800700c942c1c855200c00d44411320440e588009005400b03030720840c82c469542c0c2c1c1829880100340007000d501908440e465291134010480008018003102e642d400c50701c3d42803003600a120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 864733345 1250 864732095 864732137
    0xa0e011a030405063c0405060a11040608091c0c110303040303140307021c090e1b1912050a09050c04060b0f0a030605060d0c09060e10050706140f0601 66
    0x25560140c044c0c440b6031107070500c640d0504001c3c21010b00c0034620b101001102803008403004000960700688010300e01e890f04040c0e041100c0200f1022883c1d00f4501a160115528021a001c1e0384213401d0210345911180502c525040380d142c0c2680041d0301c1c1e40940c0241c1c90b0006942100c5600c40d00c0c40d500344189100c240740d100d000d103102c02004200c891130245000c0c00303941e02540c0d2065051044511112138004c0d202c040b1403101015501080d880c0c82c00780507040408580303540c82041d281b000c1c18401a01c0548212600c1068205c40f80448d00003030003c100d920498201c80d20000031038080c8503e05002d02424020806400225070910400d4402201d0341454004c030011140c9058034541002c141c0d04400e1910b0f800080e007002010365480000c41c0036501d01010b09050410034400084400f4140c002810320650398009500b804a1003499280c00daa030402d8030444003485180c981d8a034501e5141880280010710141c120001000003000300001c04500e11921501099954494104581c402001c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 864734595 1250 864733345 864733351
    0xe040515150d0605130f0303020a0237050f071e0602010b03071724041a090304050613150c030207140a23090a0209033a09050a0e011a03 60
    0xd0111a80c060110b241c0360f102e158003d185d030391514003100c81540c511410442808080740420342c00300380800147c2c0c2c1040010070005180a0000c55007051071041600201040c5503011003440d513501a5042084c00c6c0404603c4035041c00807145440e0322034502d60031201c902400d050060f5003540002504504c14061051480b10240c09010300b1410504000d0800c0c02e826501c01051050342103001030000e02c44603048201c4454038001400d803d00346049908104002e44200600c1003c0701440301c000e0002c011142160801c8aa16075140c20b80340140c0e05a2909502ca2031002c40c030700c94501300031034000c580410064480e0b405d03103182c16143c814112103c840c00b8009500b006400e0800c0c003000201c100100d01100c190108040c070f0500d044002180070f001114107031030043e008641c1c80030b00d08080003203071110460f098580b5440301c1a1095200070360507950700c90307503440c58000c01c4003141030207036400f0300151030040c0c110842542c03103d011040d410000e101c0d0a00c02e100f0081041c07801d0301303a00f0a40b80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 864735845 1250 864734595 864734599
    0x6170f160e04180f0b010905040c0924060203090114040f060302070614130b01060824010c02060d021b030702010203071511031006030c020c06090103150e04051515 72
    0x80361916040110740031410000019042981c82e01c043d010b41140c1c4800801841c482c03000744003c2103003440d24088045041e8040900c850030320741480001903501ca142c00c195003e2201c0003c4450b07046403102404422054002c4e60208807030b0b80491031981c00f00091507659801c0c1c8448100080f0f00803d19564452071295800c41d805004082c0089440303a001400514013138907001c9a0800c2c43c0c8420f451900e002da5046e800020000401c104000407120703c180101014200b4140c1464220401d91260000c4066040341c00801803407807020340e018000344860943c01030a625190025500030800943c40094440d125000a28a0040c2d1030702c0041119040c0d9070680c040e40c105000c2e40e95040c0640a021805400251180081c2d40d61050600280d0300ca0b58900032000e03600d0346028400703001c688400038180c045401550f01e86415440f050308540c0a64002c0c83c3c00901003d403218041d92060464000c0c0961040c3c040502041c00400a8000c4291200e082113643c0c0c1d4545014108201d0005d5084503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 864737095 1250 864735845 864735871
    0x10302010f0e01050d1505100503010b0301271d2a220c02070303030b03010b012a140d020c0d0b1906120302060f0c180d06020c030406170f 61
    0x8120910032078a1045290b410705100c1d041c01d81e05d18895040c2c1c3c0d00b82a5500041000720000c200380d1500304110709540c6101d0610518650410446000610050251248404550f0080c0f441251030405c10018a54045c504111840080080e8502e00080107a4a489842900401840751000e90040c800d00901d034035008030801001d0301404525030010f40100d450314040d84864030030000f6805901c1c0040c80503400b9000c00c40c20351501504640307007801d005000307031f00d02908092684d8002420f42888002d0f03480e400c0c00c1c0d5050120500c0c3e00f200c0c10400030065002d001132840c44680001d90047c0051441d0241d41d5544552400c0c80500003201c2805440b0000000105101c580401100340c03c1d840c0c03803000407940c141c892010703000741d00c400d6104400503400784040055104030010008d41100080c020585020400c0d40c07154102c030364001c0ba10b8410044c0c2c0c41d084c000c000b0554101da440840c00030907a500c80f40e880d88040c1a5248000da8042c4680140b00006c100e00d9285030454400d4800b4640b038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 864738345 1250 864737095 864737117
    0x515100c0212031b0a021e0f040e0c1c0c1403030f0c1e0f1509030a05031009051303090501140a03090203100e0c010315030f0321021605010e0601030201 67
    0x11a0007200c0005040b5010400079a400c011400d5801004006008000c0104a01c18410300002c0c6541d5420814043c00b10120048159540040e8120710501100d0114055148103555820568295881a400300d2100c103501004070180c0203542203280100b0b0081c8016603105c0d10400c505054102143d07258000704009250b480b0f5010207841d5044101046a480c0c0d028000c0360f6104403440e8444400c55070000a000051000c00c115540c003141c001015070105017400315507150b0701d00920000605001011000607102c0d04607580300c1004000d480300a00c5141005c000c0086046800c950590014003814004070391540a860911030b10490700070311501d401c03000042240180380b13010089070326002d150b02c9506e641c2d0b958090340a010158030003070841281001c0002d801c80352900d0302444d4040c80c8000400c0407500580c488091540c00d41002d00c80083e040001028200b0384061050116102141d0000c240040f61001c040a0380700388000c0182010010301d070b82d07451009100013030014901a0070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 864739595 1250 864738345 864738349
    0x60f031203072a02030d051602040c0806040524060703020f0d03020705060108030a051207030207060c122d1814150106050910030f020904091b1505040b07030e060d0515100c02 77
    0x10001c04451340140b101d0f50741c049d80042c0603108240e102c0400101034806011640c80c0901c60107070420345240305402d00004551110703002c811001c20b018402d000210301c402c1894001d001001032850900b0907603085076201107003d0000d411401c000e0381c01e4401d1f5030020076041e4002003103401401e42d680b262414924441c05424030448001c0485c0700b015020300c0701c0400920345016151200f80181c44100500807103c107048200d0b100c3d120f2440d080084600c10f050f032a491003403009103000701044081030780b101040390341040c0f080742c400051a03a4100b4811180c0b0a102003800e40410480b81182019030341d86080442e03180c040c00303c034142d000d001c61085035005d902a034000c07610340c407614602600702032040000074100e520f0018203640702400c6019240c16013020211840140100000c1031001e82e00040c00281140928007039251180000140082450b004e01e19280e20b401c4010030103556200401c21031005418180c80d071003103140340e55024010341e20308840744840d2191a90307108000b0f542d885d02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 864740845 1250 864739595 864739597
    0xe07081c02120702040b0303030f0f160c0b07020f100606020706030c122f030603250e040c150f140a0c020405061203040303050301150c0b060f031203072a02030d05 72
    0xc003245d1051b612041141240c806202441c4140b080e22407540b0755160071000f800380141c00820231085000303000c180241a0340c004020384401900400d90340f0050343e813240164130b4042807840650851042448081c0d020b01c1a800680580710182c7c00e68007199035400094007919040c1c01e003000883d000c001e10f1001814254020a00aa0043d4071341440c1035600c501c201c1c007010040c0c2c110845500000030000d00d400c0030820044040002c01c1401d000300200c8030101400d0529000303401ca02c0120402080c1401007180420000d01040b21003c98042c070702250140014204c2d914030030103d441c050700c09903120a800c007a0740e0514241e8894001d01007040c0e081000401c4020410307030380a00100e00007412000100007a1000e907229880f01c40d5a1f50501c42c10b20782c1c00d0300001920080141b401194800629084500e641104050301c1460f44d407010800040e0174038504041540c0c5a410200c2000700f081c0e80558486100c0c0031031414010000c1c503480c03000132031a04c003010107034040c0d014029080725184030348 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 864742095 1250 864740845 864740857
    0x30105130b041e05010b090f10030905031207030506092401050c0d09260a060902040209100f17090601050906010909051003060b0d050d0e03100e07081c0212 69
    0x10000007807414003440042c0440d4011120207020b50700510f02c0380708241c0c5920500b03000d00a5958098200700c0b6004c0000e90301c000701140360380034503090f0742c80c081c005004e070300f0280d66581d015090342d494041000e15034454110483d000e60019080a000c60754034108040d0751030043d0105294900310300060300b00d40801070030880045040110401c01d0700010710f0f09228946c1c452281d0b9440ca0f043e03a280c07500760098078940c15407420b002185036000401024000514181d460380c07010307020440820380d0001500174064594180d4108074a01c0a00e0b042c594454110102d01c48181c0781c0320f03208004032481c1042d002044401036816404640103209520307020031b0032503101c90b05140048026854105030400c0da1400c0d10003140d41049140c00740300300103440c081c1814841c0305031812403441c00036440e15981d0303800080030b15007401003010b14440740b600e00b4011861004c00c101d00612040fa1080c0c80e090f82c402d44c2c2d20984c1c1890017820601984e10251040c0300340ea08840d41d004100e01c8083c0040f401c4035500c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 864743345 1250 864742095 864742129
    0x21f020d05090f0904150b060a0207120201480b010e1b371205070509030d0521060a0e0a0f0c2c010c110609030a21020111030105 57
    0x11100c20112540c401c4038070344c800c5d40320b20401c4110000b0840110301761842921a1403082c1c1741407100e1200e0a40c000b49080c201c1e8103550103007407520524001a1400c4041c0069000720b01350501108200312018548500586d102d90102c030280a42c41c3d12005a004000000820b0005c1c140010004a01c01c001c07441c2e08188500514100e8103c4454a07020541c48800448900f00c0320540824001d0300240b0040d405101184c18950100c0e59084024044540055001102d80c2d841d400f00d12004c0c880d0003907903031a40c0040d049400002c031080016085410040e0300c440302440b03000c001da90803485448003e0141c80702411040d04242085a04912140010012022107554a1803200d00f40000d00840e030704118a9203400c028942c1d003100074501c0b002c800789990b00840c26559442800d981c40304c60301c0902500b0a807601842c200042c0007924511036402403a070b0522480c00281e040c082642500b020302000c60240404c142c0011070160b0999040e02c020344028601403004000300d040524015a204841e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 864744595 1250 864743345 864743359
    0xf031b0e010b1215030d0809010b100c14010902031906061409060114130e0105030f070605190e0406080c19030b010b0d02070f0c051002151506040806070309021f020d0509 75
    0x40780103c1d11b000420a0000005003005080c016100028401d00c80440c201791a001d540100d8a88085c200440c0420000c05e10300a00c00c80801d0b850f802e6101c01480350b401000d50744141d40701c0344100800380044805a0f01c0034078009002403845010308a1020040f0090036241d241d99960005498820b907802c071000a11004000034808200b40708600805020046001203c1e941000149490705400d40c40301c040c5644007072000c0c82000c2d084016183c80d00b09000003048420821182100c0311803040d07030320542003824030354041444030000c02c0408400400342e400d00302c00d00da001600c10100e10715104c05005407180310018009030326600014400c1600a41000d031030b0410698030fa1007c16680c00083c3c40000b5091400e01480c6480b1440044500300340c401003164480007003540d00213040282c45004c100d440e40d0b1150a80391a4170003905d00409940c02030341c200380703441d9030003501030607800004a01c6210440c160f44521800004000000390960380106283c4011070b005441a501c045041070b03100038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 864745845 1250 864744595 864744631
    0x3070c0f0507170a0b0417040314010e0607170f070504051207031205040e010b03040302120307030204140603070507062a020a150506061207090f031b0e010b12 70
    0x400080148900c51002031030001d00e041c442c072420444402c0e01540d56013150f41c003840407543e045440707604141c0200044905002030350f00e01c0c03920b03c80d9a10081c400b040c2c1c3d101c200e01c50030040d0b005400799900d01c8180c40443e560541c0c11900c2402c21a41d5403100801600802e20040aa95610780e02202d0b600700302c0d2805031618001400c811211080c158117901208060042180c1c1161042840506051081c241030a104040c0464030050050792540080440054149882007180c1c1400141100685590b42082e0800030042d600c50301a440e48002241c5072210f1506201003220701c00c82c100e95449042c82a40e80d5904043d21885550117a41d5410b20404814000140084045801e16400809590a0624003021207a8070707592421200351800003080344d2a01c805089030702c03a160482c080759417a9103841c0c05542d9000b19401c401c0e90f18031080300120811500740f01c110301c2004a01d40903805c1c2941c0305010302c0c4000d001d00804444080c01d100703045001c40701c8503c42d074008410303d1801d0100c0c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 864747095 1250 864745845 864745853
    0x1206090204030b1e0112020904061523010903030906030504060617010b01110d05030c03040302191415190b040e01020703031b0302091c11032b08130803070c 69
    0x303000381c2c106503101441101071080c5000c6607082d84007200310313030181000e4a43c0b4001c995443c07140e51601c042e004da1a417800080401155600c02140014486c441016030381c1c4503030709010150a501d41d40141e446450300400784542c002e400398402c0f00c0c0e25544031001c46003400011009003001038811602580c84000100b03400c80150740a880d0400140c0002900d401c0d901e000501c1e104c0c529500e100d885c0c00000ca0b0b01041d44d0f10800f12540704a401c86025525102c500d012880c001408400c0901c1010500781c4100b0002010340149015103000102c540d0711105040c3d8042d85c010a5944030b1003800044c012485080c002e40200e1402c08004000107500c4d038034007004500b66800030004800280d07032840e8030b22002d20340b480c4031401620b4074581181014546130114000707110b10900c00c860160b01e502d80c6010841c4411600c0100a40a82598071000060900300801103500c01c1c41d0310071460384030344094400d100315440e40c8503000018107100b44515a46407446141e001400d64010084903c00c2d4a002c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 864748201 1106 864747095 864747097
    0x6050a0b0405150c010e06010e09030909010510051b0105061f080402012001090b10081609020f1603110c04020702131a0d0b0a05160f12060902 63
    0x8110f0030111843c9801100b0300030f8042e40c2400181c801c800340205005040f42c510540088807501d880075882c1e124092454003981100e8003000400951030022152403840c0b0013801c10a1074000baa06c04501900c1c2c003d02101846e82d100d100344071641c1445801044131405040764420740c00862040288112130240001e81002149034100c2000c02c003802d40303032078980441d45c000c102a5002c5d1604030f400e00c00441e00001d1038120b001d0009803107034001c15030258071003611001c070b001c0d1030410070214000c3d0001c3c002403044540500004c08110454000f008038070717000c0d0329090303802010303030840d586480025101d0a02803401803264100584581000e00070320301440a0100d80440e249000e0500c0602e940c2c01c40b50310508012800c014040300c5041e4a015000c180000c0c4815954030b440d103941b42c09401024030004180450f0040c0700c600c12040c030450318842420103e69a070b607175201c0800f6 = true := by decide +kernel

theorem cover : BRFrame.Cov 864568345 864748201 := by
  have h0 := BRFrame.cov_init 864568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 864568345 ≤ n) (h2 : n < 864748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
