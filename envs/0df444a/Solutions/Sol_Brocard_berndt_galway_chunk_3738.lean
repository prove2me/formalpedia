-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3738
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:32:10.499741+00:00
-- url     : https://prove2.me/submissions/eb2d1f06-293d-4373-b127-0f7901d0c82a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 672122302 ≤ n < 672302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 672123552 1250 672122302 672122327
    0x1091410061a032715060108010b030f150a0801060f051819180b0415020a20030408011e0c030c0824150a020105010905160c171b0d080f16 61
    0x1140144d08441d07484401240c9440f085a0194910034140da13640011106142d0078070031004406020170101d8040b40300d6070a030720361001d204d22420400d43c05840200301c010380141c0c02408642d546090620002c4005034011009000440c1c18a91008080041825861002e0002d101c0c1c174003684c4900350000402d40245100002c0312408002401c5142840d64030a20100c03400c03225031134505201c2c0380c1d583c80c40c030a542e41d45040790f032441444064002e0b0714038001600f403ca007119100034400060003840c02d01501c0410314054820a004540c030310480c4080c0c88140150000b8503050102464141d984000c000c0c0c0c1c03180ca010140030980c03055011040ca04603000c1170164000d1a19640c08052147c484001c040540d0385500030080d0741c1c0c0e1124204202c0e24295810207440c1085800400701e036200e90380400d1214050707003c0c004518148820340300a64001a818043c10a14600d0300c1c070b1685003400f00045489260030981c8203850300740e00352030802c03000800601095984040d00c2c081c240c812401030b0304a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 672124802 1250 672123552 672123601
    0x8030105130b060f0702010e100801050111031c1b0c02030607050304080d0c020f07091b03150e2d1315020c0f010b03060606040b0d0b06070501091410061a03 69
    0x1500b0700c032400c03071032a45c1c80008203902080c5001403484050601011044861100d03541d40720b034030303403d01004441170f00050f00e410b09103100c00d001e4504c0c082e0070081c07010002c46100c0b00024000c0c003110b4102d00b96000088608060110701180c1c000980c40c0410101d6109203a858156501d64540c40e01c0681400350504602c140c0f407824022028441d0002000302c1010f00070300445102c541c1d00e481600950f28503400111800540d030031003480c103e000f900407008004032010007251107900e07851490111343c01203440081000701c000424094940d01400b814017900f10786150b00151500b503c0030350004d61a6003000340190122481070880b07403056415200d0016204040d5640384010040b801c1c080c00609032824400d000c4c0d40c0106a191030004121421034040480d040c0c24a0102c1d18000b006100c610b0f102504441c040214100051080c82099506403089940168001034400360601c1c0071469030740c02c501030380303807007030a00603d800ea40d03c50250032844100f0590b44d5650354500f002d01004410300415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 672126052 1250 672124802 672124807
    0x2011101020d05072c0f06070b0c19030c05030415021317010605030a050d050304020301060f121b0506040b030a060e04051b0d0c0e060d0b090f0f030708030105130b06 73
    0x40d48058000c140281050344d503c0882140300c88004803070458801d1421500850b040010710b060509100200c0550380044c040c0b412301540b61901d4481e14403c07981c0c03101c4a44001000c1d4410150000d101001116914080007071381785014014001e4131001d0805404c44914101e00c603107000385031301101c2c03015240480d03030001c90341e498180c2e1607642682c0c04242120350901b0804211420009205065560070400512150001d1a81034030140d0014009036099521140081500085505600008d11034803150501c0c0d076004e030908240400800c5581001c0b1404084104543da481e1030640702a40d100320f10b000d54a4a4505c3c03d280100001e51160304851184410001400004105010b0300700d4040c0307114110071b0341e9030b00b00f084450f06110002c010428011040c48000840b0302d4040d8400f4000d448144822400d490310820418101c46048255100c50b00501c106201807010381d001290a000940c00c04080707a80302d0302c483c08140180c90041c254124405e01c3e1140d542c00400751010040c00700365 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 672127302 1250 672126052 672126067
    0xa0906080106080f1b0111070902122401021c090e04080403020a12170c0a02190f0e16030c0c061b03062411031308010606080108060c04120201110102 66
    0x1d020709018801d1203810f005007005142c2c4070002040000100500c8070024041d0f103544401501d01c141c15036031b40d1060b8845c1510100f0fa4050510060022448071161103042d89040101c40200301809a4080c242060a0850004503600010040000c0c5590840e0031400789400b00c0885000615500c910940d80030f50080c4802e1140e403400500c03d890007a41c9103800151176527440055190008c100800000b00c44c21500b0300c0d8032180c8080e2040344034482c2500c003008107540004080e0740f9082d0700e11052021075a01040b4444003982c2600041408901c0d0400914040c12000c1100d40b002d9400014141c90743c541403d42845401c0409110364804020071035031480d07140d07150320320b120281d0300c0011901e03044000c10b0032034148640c1d04080c54a51441c8038074034006c00702115009242c82410300c00d8801444298010403800b00c400016051400000404914040c0c0040034000b040c1d000400c00c1d003001d4140800101d08104480684080d640050619030046c401214a210200c040004a520104056 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 672128552 1250 672127302 672127319
    0x71803140f03031005040b010c050d09090c0306080c04090201091d0f0c07120c020301180501050604062411150a0b100e06040311060c010c02070e0c03041707020a0906 73
    0x1000014964085918041c00308403200c1c1c0e03030710055401041040390440e00301710b186850f0700243c00080040c5083c08005c1040d64541d843c000b44a02202c010400b5181c0130b00400050340324080c1c1121403845e060115a207460f12042e00c3c5c0581d100d00c1070140e40c84490035015139000b00201d0b0000d26422115080c0700360103083d01320040b00306680d030b02d00d42034402000c01c0c1403500d1071054a00450f08801458036002020000340c84000e48220103e07055521121801078400b0a0034805075450b0080c40081071515001d002c000444429400400402950454544000756081c500c10103401c580c0c207000304461101d0056903e456061a8100740a0045038108560131055401c40001e00c4419215100703410010305003511882d01c0035107000d8100d4001e01c020400310300c154031024400c600c00340802d403802940d490201d09483c200c0400c400541c2c08010304004041c515040390b03621131081d031401411818144d88000304404403404a449030000460340b082907648170040c1400500e91030408019091b510742030b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 672129802 1250 672128552 672128573
    0xc02040e0f0a03021c050d090501110d0b04230105100207030209070509030c09010b0a140f040e1617040b04061811131e0504080c0307030c020a2705071803 68
    0x440040c040c0c280c1403000040c05d401c501e810b100c0b281d1642e5080c165500504801800c8082050718a9901c941c10014030b4000c940061002540c1c042000c1740c480040c500744016510a2100084030005440802c0c14050100420038103680044440072002d51003a00203d2900919030000b0398070505003402c0c1720450b5044001002440000e800759040b0340009010030902c42024419528041c10401901c250b9a20840b00d14482c03a03006209d184c1040718245035251540c0142c0c100710070448c0e200082c403421003200200043c207180c02d03182040d4961003071084c4003000d07003001d8001080c0f0700b40c501c041010850603800c89500200000d441101401207410320f860548051000d003405003081007894002c0741ea9034003401d0100c0a800d81a04070b4400180b800304003c00d0300810039944c1c484180320b50f03440700100344000d1075030500030360317421002907118010019100103035480301c03800000c0650345140700466089032036507842409100048980d01c00c0801d84901c41c1403640b51034075488010010080100c4002c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 672131052 1250 672129802 672129823
    0xc050d0506040903021b04110c0d020105092406010e06180901062a020f15041505070201080a05180d0c05060a02030601081305030d0218010e01020115060c02040e0f 72
    0x400e000d6038888809100488038000c0c000b03001608106c210b030804840d01d00c5013560030071000d0400108814001c51100464008004064054002c9050000d0180d4240030749ca421402c42e07006880945140304841012a0002566901110300134000405d1603020300c0e1480003540e0044d0100f5940d004140d00240301e03191040700c0b584502ea07000000b0600ca0304c40d05110343c0c80302c200c6035481401d540c540d130000301c251480744080b6440300b012103e001c940d48030008a2080881c4222505403214148104840e0b41c01900c051101082014099900507030381c0004243d811103150400099562242200f400f40342218006c0802640315154160452541c01405010300d0b500540590f459515000076070400d0b4131094521a0014403120003041c10890504050b0300300c248207004503071a0060307144800d0140d81012030301c0703844481170050154143d60040e02c0c00a6200c0c00344020822039034004044610090b560081e0003c1149441c0300c5801c545507a4000341112121204842e000c8032143c1010b59140141c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 672132302 1250 672131052 672131077
    0x1e1c0302070533040503090d12020712080301060e0a0b040f0911031510050d060e061c0302030d02090604051f090b07030c14100c08060109140603010303050901120c05 73
    0x2102001403c007000100200810a0b020789900f41046001c03d442003102410988542c0000c01000764956106000840c0e05071044100f200f22044821002e0306103100765200d0380c4052907404041c1d0000c0d113541c0403203042d00c0607402c00c203100745503000102c4c190150703a40000c05407082c0081d002c160010f040c0041c0c0d08650304110f050001850080e001021404140c50010022020001c4415140351030200d0300c413800b0342481c4c002c0c1031007841218001501e17200e502100e1010001d205101040c1084c0400c203807007182000c01500d1150560707800a50328030a032040003100a5011603807038103558900d000c5a00910000300040c0040c40341583c88500b0941c00c2c10341102040b003501001440a80c0802540d070b1403901501c8040d05810789490b0f04800c1e411ba580070560034010080c1480042c0c0e2140309410840000d61b444004c00e20b4030134009415001142c1100300360300c0c4100e00d10741c042c2e070380c11040b03d0640e42c8c1031421a895046010050742e000307a92038922800c06080c0303021948460b0703100d4060700c2c40b0329081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 672133552 1250 672132302 672132313
    0x50601150c0203120703210c0e040504020d1709090406060509010602150f06130504111327021f0201090309173f0702040b030f1e1c03020705 62
    0xc1425512514591802074054002c1600d088071315205002030030712640030341400000c400d080c0c8625420200d9050403001466695a80354a00c0d60307002260000e84402560708000c2810300740c00107109a107062200400f1101c01c0480540218101410b9031200070380500301c0080b608203481c04030043c0400f0b0107070b6801a06800d000080d0300b44001400c02d55109c06080640450310b400050f189e001200908840c1c00c03039140c001c9040e04448030b20619110f64043d198141001034030b041003011040704001d940d9142c6040c80e008010449101c00050409824418800d6800c1401e10118001d104c200c081040c01460304040500859010b4002103290b40c4aa0f503280030660b03c980751344140386100da03952402c44c0c0c46003444005800040450010585140c1c00007003442d00b4071041810720b88100342000004140100d68031007141000d00513501225000c03005404a4a80582c00f166100c006072486000300456042e08003906005200035040c4811a00207003a404035085800ba02035031001030101d9451291 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 672134802 1250 672133552 672133589
    0x100606120522050f21180102031c0515010e1302031e1f0602070b0a050c100f0903030b0a0602030f0a1106070f02100b010519031514090c0405010503070c050f0a050601 73
    0x102002c6550841039142c50390038089001242c200421240d0b0b111ba056120030814408410303010341c8010301210f4542c0c4045124a03190b01440d00c0c00c030299022905002600384001601d5503150401030b84c28074503a100584035a0380c3e07003400921046201d400c10414030300741d0900200c080600060340369949600e2108100c16500c03d412070b07075008284500e00c0451004d0108100d41481349000b0003245849c0e5084611400c0c5000c441c400301c80f2500040251565907c1c0840c1c01c260f007502810031402c8084407458070300341c0761610181d141e110f48041d1600c50036000602d0717000c0c280550215000c103129601101c0300d40c80c0c480c50160500c071180c0010005880365030800800c40c0c1d407500401d40c420b4010307920607081c00011180c4646221905403020241034403000f900c020040c03401245c000508009189090300c05e82d02d4280b01448901410300080c0100421040c4011398000080f04d4000f44245000d484022250401900303204164040441700c2c004e0200d02c1c8240714002549034140d456542c0541082d100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 672136052 1250 672134802 672134833
    0x207060617031602010f02150c030105030c01020f0a032601080105060103050609070c0209070c0813150207080a08070f0210030e100c090314010615020a05100606120522050f 76
    0x2428022002000c543c20a07a070055110740b038510034141341c03030040f0f03104c0b040180003013002140101c665041450001c00104411715040020340e00380513080c00504100c40412265945544c0c01c010050140841000c50b0100324585505520f4070401481107070040c0e503181c041807406858213884160005e41084080f82c041e00c2c00c228481d001e0071258440001410a40e070030701c498003900034400e900340034850250700d01040524006140c00380e610260a091141080d0f00411181c40085032002150310480050010803000100f001c0085e030880c80c0036803a600d091500031101000d001c0d009411040300c003404125550190444001004544c0a44180c81c1e102c1d4200c03000c941120a440000455842041010407034405060b40386403078080000c114a600d48a42001c400317441c40749400140e05c040f0010050000600c6108004a01c04006000213841e041c0024699641c1040c4004032a98a00100d862501042d41c08428415032001004401441741085615204440070641c001c0c05800300c01709007411f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 672137302 1250 672136052 672136057
    0x201080705030c030703051924060216060e030a060c0c1a0603030403062705030d140f0109020d1b050d050105090903160c1d180109021309020f04020706061703 70
    0x8140d840301d141150740c4c201049015000190a4819150b074242d01d4005489030303270165080b080d00c40c12003210004a002010f100b0b070380d1a5445034003190031079440000d500f000241d000c0112141803404c0b1448108503c0001d0a140c1551001010a40f604490030015504000c4011501d03001300c1983d080c800e01502a902413020032140c6541c16081000207000041455000160303440040800c9800b5103401101e44c03101c2006258199025030021030380419013900ca019100501803140c203442d40c5400e20342e860b540411010f0141c9001c00c4d4010030a04000300c140d41c84090748500055508160070401d9401500c2c03640b18900030f14030ec5040c0400410b45040800c3c2040c050442c2800541c5402e050381884c01c0c2d8618541406c55090000c82400100300c0c1039145c03245103c036041e484000c110b0810311284044404c00050210343c41e41030000caa00569240d4a01e040c1000e00d44401003450350043c40050503001c2041c0045ea4410f101154941c24400076900c100244c1c0c1e4880c5090494940341e0901075600d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 672138552 1250 672137302 672137311
    0xe130320070915061803242c100c0207030f1b061d0d0b01060302090a170c040f0e06012702030901020702091f0b0d06030f0b1f0f21050712020108070503 67
    0x312404050b03164544071460f00025801c180002c00101440c0c01e0140070b40b5000108d9010f0300c000f801101396804c5140900c840007401c17034001700c1009060094940071392250b44612000c0c0c18034014500440c02c0c801e8055641c042e41c1d40381c400d038244807074503880054001c100c80320070031001d481100c10462640c1460000051a160071400e100e036560700e0103030700b14041c2d1302641441d0341156148000140c036103600c00701c0ba2034600c50b11016202c0d01201e0b4040c030003247c0c000b00c1d03402c46050400d4803009005001141c2c84d415180102d0760302081d003c4140000d031240c01c540b80e903500902e10010412600c0071065014095a52003100ca9441986488545c220002e28603250400802c0760450100212108100181341070b5240243c0030541590382d8a958a20300d010074410f030340c645050010003041103028501360030541d2480102441070b40c1024242c04070520303640200d082e2050080e4001d03454550f940c0d1a0404190f202e03049429541e250010500425000c2c2000c902094040d4045940e0302c3c09642075a208 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 672139802 1250 672138552 672138563
    0x91101021b040510080703120806060a1211041508010e0c03101205160b0304171801120b0d0c0f0605040b0f0702130e070e130320070915061803 63
    0x3a0200c0300400000b0040030b01305803000c5560075000a0103040903c40e64004600070400700a07200120340b005010348a0050000c0c1c0300b840100300c019000758215840a10102c1c44541c0080d0f41c82c2c90300c2c4256210304c0ad9411042d001034989414440d019888200c5174141ea000e50724040f025200c0303010310381690000f42c0b250f40174080b080e4000e110b100700340d04009612a02440c00c59040c41d0482404036100d6903070b0740110180d02800000c000a004c0c00298040d015040c071142d0a1a2040003c00c40011000005000341080307101034803101c2c41d80840d005010340c41c4004121001e90705541c80c01140444a0344141558442c4540d03001510030700910a48044813404030000e8274015080c8607100165001103400c036071280004d0f0440c45004070301e1044450001c102c1c4000c00c03416044c0b030700000210740014035000c1100c410700402800240d1055480e80c01542492000312074452004075503041540d40d40180c5c1c01d4501c3e1600884515070350510f02411103072503403a5018090003860481c416040c1a001c058403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 672141052 1250 672139802 672139843
    0x12306090306180a200f0306040302100902060c030f090a0602010606020c06070303140c0a1101050c180102030403060c02010507031a100e01120f0c092108090d1509110102 75
    0xd24000f4030f0051a14845001c15215841e5941c0d613132a03160720b010381050b2000e4100102115050408600000319540110b0081005282a6030000d40da600340b10920201f45465800e42c0c011519654280d0310220030300f000752512054072080b801907075009114243d220300c0307003602c0002d60140103204010664205a021700b661010141c1803242690050710304404240e62803440c001c510300c8443c0102d016041038606565a00480780000317260380c107522004059039240009100301d07009410102c030040906151103064904035540140d003540919070000d013559040035100c050565065120702c0c440c0c1216101000750111215042c0c21807688410950f8102800741d0b42a20414001d0b1860703406501d0501d00341520080d8565000c0c02c2c1c41c05001800c40e080d44400f8089ca403140c0141c3c888015101e484881d211200801a5003168030101240241840740000780034125519000c020440c0c0da900b01e007504d00b4440c5400240e0005007610311066900300c180c140010480d40c40481c020100c6604440c0f90708 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 672142302 1250 672141052 672141061
    0x30f070503041a18010e0d0519090e040606050a060f0c0303090c05130e07140d030c0335150a38030901180c031e0209012306090306 58
    0x9035540c0c409081650f101c41d2001d1403507601901c1014051003000080103040d51071a49480d45400d5806400032081d5941080c1c0da0641480d5001d0142d40e00c4c8080760075019032189006d0f400b0358031107241c0e801034054100e01c641000107014154000c0d80840f18160f9034441c00075038840c4100c50110031404180c0000304140040c0300402c0c883c0c0c200c41c02e494080c0d440f8510680d5100c0008980c070503501d40c0c011080340c549507034016800050056800402d000303403c448007200684000303021410010002070a00c03054210150030305102d40000a120ba0003a1310791401100c035481c400003000d07030b0b00341c20342120302c0c0c1e00c4005814289900c142c0c03920244060000d214042c202901c2c61500003070b8591546c1049918110360004501c00b8529000d03c92061045030b82d81d0a0100b410f500f55100c82c00c003480d014003003c2410740080c81c5281030300304072608006152595805408081151010b408000e0750009614001045020408003c10f14000140317945c07080141300d03c03040c405a8021911700303682c507811648c0040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 672143552 1250 672142302 672142307
    0x21e06060d0602030612030a0309061811060f16030e2d0d0302102f09030d030b0607140c03070e0f04080a02460b1513090b0f0606030f07 60
    0x2590045e1000300000c00803070044e5001490b40c2c0158420030700280e10786124900b0b10400384108030074905416641400505103450300c8480903100d42039140500350028505015800000944044402e500c0c3c184040005a05001300a02400350b1032a2268031891500c0c0341d120044450078848400c480c0c0806490700310384081180080340d03000150190f0041040c022046004c1d849a140d40280c0c0e22611100114000161900c1d100201250924440304204040b4140d40004420030740c1101ea14001c90881c24050208a03c2d000c0c0603401801d4140c44846190108400f0500503601e01c416011500305a80d100790070240d184054030028009012503001c2404901c0103401040741d0081c0340100c51103408a201e00503010300c001c81e29008102a418841280104401100c0b0a01c00c01950903480c200c2e0103442d10800b05801400c1c0d6903500c485800307104481d44445482c0141c5103041e4408000c40c280368100104103090444a0319480b46c056800108145013034020ba0740103d6001c541c903807803940e65403000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 672144802 1250 672143552 672143557
    0x50703030f260129070b100806010e0c0a030908071412180405040201050403020a090b0f0d080315010210020f0c060a0e0d0c0201031805100f050105220219021e06060d0602 75
    0x10a2480f8400c4d03001c82e4040a40710000704a454440e81098143d450243c0c0c80400c3d04e0120341011006030084001000328004045d40b454100f852000c10581e1440d000c4002d03402490940e1004021100100c2c012040c001d0b210110001c80700b584083d500240c802d8140744c411842400110200c0380c1010050442504103030340078541c054410f04000c0c2c9003039100c0d00001c4030109942d00c40501c181d114084500c05082c0f4a030070741d88401c000c1d0b980200684031580c518505000041103007040c210400d1803c02030ba8401c01400d07001310302c0e8240c21580c0f0401784400c1001544221040405031240e50041032210a0510401c16a80d0104010f40403e1201c80c0d030481c0c07800e8001005034101510368112a0501d60700c100742240c603610500c01440008080c981480681e28031070031200c1400c3c0b41c41c5c0108a0f54544414a8800900c407014020551108cc01d003d4028010142c07448200c00c0c01032a513241460300020f0006480c0c1c125120301000c400b07801280340e43c0303240840702c2c960070001410702d181c00220281c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 672146052 1250 672144802 672144839
    0x60402010314070c1b0f0b04090b030303040308061c0b070f110c0102150a060306020d020406081b0d020904090605131713050103050910050408032703070807020d050703030f2601 78
    0x300304940300d99030700c1c0c0006294100d4200c41c0447c00001401c00040449124185800400b034026506510306504e0103466004020410f03400381c0b405440c032104082e543c0f41511200340d0302c410140518103015030000c1129820001e9100406da00304503940146000040f070b01041c2d80d050b030085c14517070b00c1c0c407001e44011140a02145661606c3d0a0b0110004206001a285011400d0030040c2c503a0310340500240808400f0f00002140300e0128005221080040229010b45410803809030380e034004c010108004140b0503a014121501c1c10b800e101d006c2000c15610100c590142c1000e80740502400c1030880d4a00c02d000e410705602d0241e581c1005254080c0c0c00050384100700302c0035035455026100031502034030012242241e40000000810a0a524100c6132240e0300d000e1003142c01d080d244007060140d80340b082500c068038021000c80c3c160110b68038008442906688a002c2da05060742e285005030850070a081001c0200d13450071844070340407200079001ca00307840021a400c001030b484c20001502600c0c070f119 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 672147302 1250 672146052 672146093
    0xf05090c130e0a0f0f0b012c060c0d082d0402060708031501030f0213050402030c13030303060e070e0108071121040305151303030b0d0c08060402010314070c 69
    0x900014601110b031024038411049040041403060101c1040811981c2c5045000030141c5041c281240301e9901c001141c4038240b840d881d12010070030380190a0100261246d607568822400544805082008900200380f0506030f116000036880740c42e000d0403281603040f80b054001d0480c00283c1c0c55850480308040d0001c0c0007a003c03d26150309030301d07003c0c2c40390b2048440896180c00071b59600d500f960b040c411382c0d813079080781c1c01c085003004010b40d184d1441035904d124461041c0e40200200d102d0440b8901100e00c60460700301c980000e03e42d02d280c0600680502e228842c50240440c0c005000c0500503030241255100503507a40d401669010720545202022010802c4c052080e0030012032091403640000d4003070042e041086441d1403540c90041d141c000c03011150b01d264403d100074000d800a40300b8054075031940c10308001c603806040c1e00106000096907403028044081c411000100c0c94804204180654006c6c1e1b01070256030ba040501c0306903200d041c1c1d5803400142000701c611001c01c84400050884140d00b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 672148552 1250 672147302 672147337
    0x910030501050919091a0405071424092206090603080901051608130305070807030819110102030f01031a160e0d0605011d09061018090f060509070f05090c 68
    0x1d40710299109418000465240e0350301c411f0005124080214000034107031084034200071a600c034081010140d94060044900c81003c0b01980100700d910140c60783e0100c0549074030002e9102c0c0300e03940c0c810420b00d50419405440c00a0101c2d420185004031303802c1d207800c80c1c02945060f03010401182c146d4000902d000c00404001c18003000a44244002d000c010b04040c0a82686420760410301e00f441d6280d07000c51480e5211010400000b205001980c5120b01d41a400501e1207026101c1646ca4001484440049520020800c030812000141c2c143c107807409001400010000d40244214036142900c006003101a9031402d4030555208401a21510380d019080c0d14501d01d0680d070f21f005990080c1c00c4040c030780200c001c107840712001150035154003038100390082055080c89000a0220030803030041e105c03030718221400f0640141803034216000d10f035400f1480c10729a99043c10003034001c0c201620300500701c0c0034010001680d412051160016030300e004000d07882c0350700d500c1c1034080c03da4042c040034555448403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 672149802 1250 672148552 672148571
    0x80a0804030b0628060311030420030709050907140d03120f021312021507030e01050d0e0d0815030c030309060304060b030d1e08040f060507020f120910030501050919 73
    0x844081c2c141042c000c01c4c510009508101000c5d0580d20340b003c003190303842002c3c000c00000c00d020074400903000c1c1c2c4803070041210506043c0404c1c140303000b50b0080d040342c508020038015003400000b10141120108998910520003000401807400361865001d0b0000340249485202404948d00c0000f4554100000625180070240f80308032443c000d501c11895003070300500e07403010341c00c0a00702ea110300b00100310103900d041120703a0054103008203003075014104140410846100c180c070381d000c00e2520325803800700c605070200c1d010000e15001017200d161010344104811305290781030000d1034003483c0000134051804c2c4155801032110642004006641a079140e0f40400002d8502340320100f00c2041c941c0d19030702e00104140c851403c1e04800e954200030441c41d40c08106c041026007424015542e8004004100e0340c07a0094202d2904182d600a0842d50140c0803079000c5058040c07004000ea03660a0b10000c2c092200b618041d4102c540920402e600040020001602080a00c0c041c0501e004141d41c001041e450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 672151052 1250 672149802 672149839
    0x30807021906020c0d08131103121605151b0f040b0408061806040b011401030603020a1412010b100c0c09090b010302181b0901021903090f080a0804030b06 68
    0x1081c030700980c1d02690000e01c00003403480c10311068210a02c181085d298504222180c2c001204580001070701a0000811078883c07540d05004900c00b034001c0c4070b64140c90b201c8405402d159200c030160200e40c01d11995072034204500c111300c401881401819101c84928078a05403421142d4040c0280b4030f0311002c100000324030f04205c080903001030408000205140d103025164031030716102092500809034400d07820800000c52030700072241942c1070f294104500ba901100160b016100c107800c0250f200c90302e034001250b907440031046001c0b0600115000c0401a4105c42001e088645198002d908150031030031079400c241c001d84804104030300c2005214421a078801c0c0324022a07a0f100d0003103134420001c000410640c0b80c0030f0960a6180e440d00d0441201c0d040101d103400302c2c840440302e418a01c41c000b01d00071342580c5c000c1c408044005205004003031004180c0c40c0c010301644243c092074410841603200469010000281c005000341d11081841c641419a180c224642800825aa61103020b01003207010550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 672152302 1250 672151052 672151093
    0x7020406080c0909010905061504180501020a0311130506070c0305060901061403010509070612022b0507020d050304150b03030706090314070c030809010320030a1a03030703080702 79
    0x801d0041c1c4a07100d890010024142e0b006440401c89a0520403e440400c8001c20290740008010010f00494024080480c0150004c4001c00c0c01d000908062a01448019001480760014030f603420003200c1d001d0714140840d0701900c00032158094250200740801c2c2022002440c0d034074020307030f1800721181c1c1e01c0c0c0c3c40351b20b020360071900585240d44a5000b0003480d02119280c0702d4000049000340620300e03001c0e100030758400e601c2c0304510404c035000c0b007800b4058034680e0460f030384100005548008038070300002c0f20700d01140d00d0307110481251074100010806417010907202c0d441030380f5540d842d2a5880d607403204075681200360076802c040f60780c0702001c00c041e07a802c00013414020300c54500460055024200035080702e0b1420218a250f480801c5504000341842100e402a00e42c404503107604e8801344801200181000b00e0b22a50054171800c00100c2d003043c0c2c0f00614072a855480d814405008003900c0850f10404d215620f0303805600c18403c0200088c00360200c1640040b25204a074021007030b0840c0241c03601c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 672153552 1250 672152302 672152309
    0xa03021308070f0b040e0f0a1d010b0a09110f070201120e0a030206070201060b0412050a0204050403120b03070b090f03330f06060906030405030909240409080405040b0607020406 78
    0x6a1140b1000c2090703d2002052100605804408500f414604195261207040041c14054014503000001e04003040540c4020610580d00414581c5141204413250003002103c0c61140301d2100c6400019541e1030b1802a100820b450094844c240010200e071001d094109480880c1400044024612109c2d080d11500324034200d010300038018400035003006420403d006d0319038411641400024449803400c030703045904440d01d21216102407000360901da82408019080250302c035080c0342c10f106c18035a109800f0884000c85000411290412104055540015203c0d805000c0300600003003426240655240b00411710140565101000a00020b104800c14100b4000040a1009620521409114410f074000d045461800190410f41c00240240c000c4040203441064000000307000c1000a0083d50410345018010034064200a140d904151f01d0840b0110340324503801c804000c541c68540502400c5035001400759180c05d050400307000107000780001054008400300040c1300161118821070006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 672154802 1250 672153552 672153569
    0x61303060c1706030a020a36050126070b0304050c03010f15050102010b06031b1207122301051e1315080328140703021c05130b0a030213 60
    0x7074550310442d05207190080e102c0c601a910400e01100180c03989120380d01940c20061040c4444402d003960040c0c21394004011100c40c10320103040066504141d0001816941c2100c82040b401b0102d5600b00810525400c06940d180d2206404000c20050017004681007405136003603840c1c80b848000403a0a580b2110502008036a854030700c1040c601e80707072600c1c5c00a824244024401508800000f911b6408094006c551708600380c140f15403514404821905403005056040125260056000d0441d8010385511201d160030030211131383d080c1205001030780c089a08001c1c404a80d083ca800d01c84030b11042c20510703014898241e6204010381ea02c0141003106c804003000400c01c622159a00c1c0301203041684044070b2039205001c507200010700c1d41c15043e0b040f50505800a1040c4151408880303400801c6580d0000480001e00c5030103144d13021070171602c806010302500480e9115000103c400c0d12903d0800b10401c915841c00380031074941500103000c80d101c43e00c1c015091910310030250340101c00c02c1d1700ca001e2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 672156052 1250 672154802 672154817
    0x90f0418110a0f0308090f030a1a0c03091f0e03040e04050d050702010203030a09110a030303021b12041a07060203010e010303030b090c090409020114031009060f050f061303060c 78
    0x10411116560301146000356112120b9616010030400c0311011808000c0903800003080c0b0340100d40b6840c5000d00b60700002001c845851502e4181107114214800c04a501480300c1030004412222150440e40900e020400030229440600a808070411100d9081c1c06403c0d180c0643e45181c5504001a00c094030800c0741064540c18a460100c1c603044002e0205014000c0c1400300c240542c4e00070040e6a4001c01c03800c00803481c07800700e02c1c10410700000c8a2425600482380d800102c24941d01d0740c06000f50599107902c038070041a8201805980c3c0301c0c00c0d104010141c0041109200354100e24580141280c8000704040c00d1103501c2d5154030698109812441c1d108031102c00400034517525001d001c2c00003900352017000c1c2c00d0501e03035540350403803060403107080c0203944801c03d9a003164814101c0d21088012101c41c00d032a41403190078000c0d407520a125071610035041c05404561035090003d95411510000d08225807100b0301014000c0c03c0c1c208a090a01604040f8400008505180640c1c070014400760780320f10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 672157302 1250 672156052 672156101
    0x612010c0e1801060e010c0f0605010b0c061005060a03020f04230901060c0b04020907300e0c0a03030305130c09201303060e010f0e0d0f02061506090f04 67
    0x40000b1503007100e241c0110800402c41c5940252441c03504031401e2178010040c0c4140d040c018601182c0d29401441e141c9050000158106040080c10030380944100707403503241e25100c00c00c036280b661380d02030154070030f00800caa8043d01c1e000c1e9004090307102c85031101c14101695280c003010300c1c0c82c02c43d481465013502d80321190350310f141400c010740c00742509080c111006903140d1981080a000148020b0190001c03c000c54040350140d1200c9400c1210030700d51040e1004612442141100711038550100b003800c0088080017604042554902c00c2005031454030090f2131502c0850140c04003818942e21004498416404940001e000401500c990800402c0c80b9004045102c0448040c1045209151007401607805010080401004403500507002140c480c0c1018061401040600c5920300c1c00c1c2c0c075216010000c0800030034043e00f010340316151590804a4007409070780320307081122010740020f8600303003044880c90701e80f025190b144001b4002c00101c95095000c54101d500707041407204414174010000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 672158552 1250 672157302 672157309
    0xf1f200309011713020409020604091805010e010e1015050603040309061416140304050a030f050705010e010f0f170f18120f070f02032b180e0612010c0e 67
    0x12140c081c82c503d408501d0b140c40704021306a4544200000d00c201e450b0581c01c41999560f106a0b0041e06030550304100103c26000b11010704200c1d15011295542010100c180c512010721410841091080190040458160183c4010b02121060560b03428401c10081050b8452070041d40c484c9100b40c951032101e07070400380d0140450041c01e032402811081000482541c040d802000c041c0c05038044011824001d4030f0107250b0440c022a04415000034003148004203001e601c0300000e801c01e000d0030940740c041d44c417000111241c00b1141c0615010505c3c905c00e540681c3d00c5424a031481c41000d141c40c62507100d8400f0180401d00e026584410070300448800c0c042c54408841c051642459a2001000e00c4003804101d5481d034022201c1a82d20444081104810f12014045180c2c07006e500600750b8400d6002c07140c0a220034800303541e078005450a142e08c034860305801641903c024201006101040e54500320340e250100d000100015006910084100c80e03a000902403091a00042e0311241d007404140b4050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 672159802 1250 672158552 672158567
    0xd020c1b04060b07060507092111040606090b0705100207061d0d200a060c03090c060509030604021c0f061a0402070b060d1703040c0609050f1f20030901 67
    0x140c0d01c5186002c000f00140a050300c02c4030701c126030160380854107a454039015038104101d98802c803440c5100c0400c0e0950680020481954170340b09040010032116150140002c170b40b09401090007080c5401c100b4080e01d0645c40103060110300c584111101004128500401d0341c014090884100381c441c070717940c40050105502100c0c4480c5e0032000380031102d201c1c04000d000061034244c101071880c50b40c1082c04944e00501801d02c103a504802c003171090540d4100010024840030b81c040d20300c21800b1002141e1a4424800c0352030100000740241140e40b255020401341c5080f64004000030011403130024002001e0b190140d000c41d028910002d119110301414020288030104450300c951700c1000352100203100c040c0040e0300202c0039102594000b082e494440c11650788001054088103001c0200030400070740365018000e80f2911345d00c000e8541d998500b40404c15850340012a4407860a501c1003c00c0c81d806261903400404620348031240c0e511900340900034819052400d04690000101e0303400d1560081720 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 672161052 1250 672159802 672159853
    0x3070e060f0720090912090406050916031107050c040f0209130603110d082203150c020c0126151305090f0a0b19140a090516080706080c0d020c 63
    0x184613241d80f5004034816122055074240814526011403580703035540303503544800c02400e07000c0d08641660419200041c10850040310507030000c1d0800d12020703100000c18003030b0303450160300c00f0044c08210313072100400003d0b0180e0601512010b070b00340300c3d681c1980c0d155004403159404008001850504600b80210080c41208070310340101102c80030180003c19031022a039882c00700c3c40071b1620f54084444e540d00d0f040410390000d081e440e0114041600c89c6116445a141047c440d000c4412003440d600065a40300101c40080e020060080c1003001c0b0342c0907101c1400d502100a17400c1e0315070505020000307001c14000030051500e0301d40d28420040e1400e030400c008070b0304400c450300401c4141c900f941c5130225038800400500300f070341806000c104403407000d400058201f40d50081e00030040c50518501070050003440e4060701c2a100b00b800b510b500c0c402407018941902c20040c09002c04508044055810210203018900201003c100324203228103203202504103411500050040038001c0400000800d05184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 672162302 1250 672161052 672161059
    0x305070306050112020c0c030f07140a0302061b070801020a05121803070201120b1c030f090806070c0c05151210061e170f062403070e060f0720 63
    0x4014042d07680c1180410300040615503002d0fa82e040404081c038186000307000070759014802d054110b11011408101e80c402d6030143d140c00c8400d22061010040103950b03d12000e50451010000d140036042807011000305989c0b044100ca40b82e81c0d0b100303203680c01c80e0301c1042d0110014001003009030350101c1142d04039030042c8280f41c951400003610403016440340701e000b500030f0501040c03501c0503014000c01c1e001130309008002040240c2000003101c072a500d507401004100c0c0003e40d680391000d0141e004074401400e4400c03510041040d0303030340c043d02590304480808040d01c4d807003500c02e0006090b03076803001d040320681c82140b44d00c1d8640401d600b107000030050141005c0d01d5400188000d2021591012040804d0790200344410b14050060340203640984d0904040d219000c4010104520340e041c04208500501c0e0544880142d41782d82c1115032201541c1c1d042282c440f81e0b041000c220303210f1054166084200c0004c084a2500205941c1442c4176400080120707100499100c1c0c900e0002440000000c3c01c4d28242d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 672163552 1250 672162302 672162311
    0x1b0f200604050a050105031308040e0708010e071e050403060509030c070609120605070c390503120c12030f04020102070b0901051c0209100201021305010924030209040612020103050703 81
    0x70b000600a9802c0e020702c60403c013002c40020010100351fa0340c400420341181100780e4030b503280d86105095802c119400c1001c9501c2c4400087c06164085e400d41c494203043e500c185442035402c4410301c031007692100100070060140800301c0810b0a5115440c0034600550085070b80c2c45400ca041da00713202159000380c040c404042c0f4100b2104103a800e880209aa0180740004c082d901c040082c0c800f460741c0940506000c00404c070031088102c40c1c0d016031101f5084842d18280031290001040d401d0030302409141d8240d04507000b00010b008014019044860050f401d0360200915918540c01c2038000701c2e01c1d040e070a4a10b005001c01e558040c0f000703e015100207100280740000350710002e0014400c1411380c1c0b5a030100401c10400e4202c05505454aa020052110b9505440040001d000c2d400c083c02c05030440e041e80704009000c0d23004540c5202240d5100b0082c144c00c44040340344441010178910448103142e020402e00c560342d5514401c5401038110000003d080d2000c80c0001002c0720001060070044c5440c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 672164802 1250 672163552 672163559
    0x120905250e061816141801030b1c0f1a040f0b100f1401020c03030406120e0d1b05010f110d0c080f150118031a0a09030f1b0f200604 58
    0x14001c4a940000004080024002d54001c1200e51715440101040c5080011541802454041202d00340340e0314260303001d003c00149003042164000480002c518141041d000800016141c1d00b80950261b000d0080715503c030304d1104940150301d034100c4088400f40c00e202c100c00f040007555810300d6002080c0702c1c90203144504000d5403548511407805170402450400803e21030310b82c820420b02c04000c2014007900e80b138503551040944800342e00c0a41035902400c0504030001c441d4001224166420300742d030b43e0031a45416020303540d011180c42100b502e55540300c10084150000d0f40c01080104640b01701c00c190303101c0c5a43c807111708940c0e0301c2242c6800c1140f06028440d11410440200750412500542030318078441180c01030b141002501402241c4009582c000400c1c02040180f40311034900c009440d581310b640d52602e070b070202e400e00c0310000c000c030381c001c000d4400b181e10030803041c4100305126128503284046621003010902c0d00f41e404403205000c11f0b22002e44105080d840e08407040044e07038900e00f01400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 672166052 1250 672164802 672164839
    0x1f0b0a1e08101b140d09030906020106050102010b0d08030403050f210c1e0904021e030907080a030203040e0c04170c01090603140f040c05060a0f020c01050a120905250e06 75
    0x3801401003080000d0796413002840151394045a0380d10079014020070241d003841c030300640680d100b03120305c0c0050351900800017615401805040211000108290b043c02520ba92300d840725000a4000d40c100b140a11111032180040c070028500c205c083c4401c64075907611040d007482e00c036000900440300c40d401400741d03036030380140440941c90700c500500300d81d5107618038200814028000d048000b40d854210748507200044010200643c000d1201005481ca8991202e1429a4031785400b140180142c0c010001004080c4c0950315aa03000b240d126003036840c20f9a25804480c5620f08190101e0864106200302e548542e00000208000c0c4031a040c2804000f408000c0c542c05610b000781550011841319002034200710b0180d65040151900170900c544601d0501401030451012074050405442901585089503005a003031302d44c0310040b0360352800c0c8a0741e1181103002030005500112010320034022402d01341e1002c003102c88181100c2c85840441c0610f400c1201490103405031aa5004045145d2a01e42018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 672167302 1250 672166052 672166091
    0x10050906041a0406030c030507050307150509041d0c011d0112020f0c01050903031b16060b0d050d11011103011d181903111f0b0a1e0810 60
    0xa0121030004a42c0e5651201884141c00031021a92240c5040000700400c8102070b910390a482c0604121000b0366110000e15a40d07030441e0040c00180040c0c08000341100d4880e6000300054200500041081d800b280e0b03601c43c051070301044081d0190050028140c2300e5a000b00d080c040840100d00310805601c80c2000a09480c41e0301d050a0f01d05500041d5000d6005881e0040b0741c0e0b0074413080700812451811030302e45601c94005441c2c0000c140c0c410b0000300c03420000d050650316000002006002c3c0700c1d185a50f01030003000ca0100c0950440c0001d950b5801060050142c1d60b00381c4c8840d1102d0541d00035440741d5608441d00d502e40454211400e00c01070021070307440b0040410301018080000d007140c44481c3d018140c618941c0316442507124180d00386130040440d1500c0c54229219844d4610b860706d00844098613011403056140c0f04140f40440e0f0301c09115039800840c2841c202410300d4500c2500d40c400d5091802d0400c00060392240600800c003d450300801070320061100d01581040417006006030049440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 672168552 1250 672167302 672167311
    0x20730120c050403150c0f03090b0601080a150b0d06321f0c120c0f0201050307120203010305011a0a030c140a05120705030c0315010b0a051b06040605100509 69
    0xe60795807400d04030490180d021a0051034025003000c01114a035043d000151242d00c1200c00040e150100101c0c82c0c502038018504010362114503011f5079500d07c0c004503641c150040c900d881c10360301d8006411812800201c80c002500c0070110040d66503980045080035102950b129900041c0d04050500d009000d0303001c0388100700740c207180e200701d40400e00d0005500c00d00e51800340e610b500341c0b18201c000450f401c5410802c02c584107050340ca110001400e800e50b200d02d04280d000c0d1080c001c10055500640c412001941d01c401c00c1e0400b210003210b00c181d1081241c100744c20403565695900d103641420700f07045101520341d000c11900c1c00300060860355507607030011039803055640004601d900341200d6503031385860502a0802406118401107012079240c0e499000344182ca000c1c0c01010045c20480c1004207141c102d0b0071140c1d81c00c5101d85d04e032210b00032141d40803400c464200074050202801d00310000d514150240b500c01d00502c49030034541000c40484901410020500120036810800b17920b1360358996510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 672169802 1250 672168552 672168587
    0x130816060603020a080105061903030e04090501270501060b0901020d11071a12101a0c0a080c0604200f011803080d091109040503031b0c01020730 64
    0x810a891030000041c12054000070f41c48040c03940003040010056216038815101201c08070440090b1280b900700c0c5000700e000250002c1c0000102e00c106050540002c5000742c46003000150441d00003010301040740c8000c0c14140016520b400c0401808001d0203810702901c10020350616000d84280080e540d040309a1040060040c82491254946418041c402c0100b04040050b0412445071003200b01d1076000c0c04c0485078100c1103d000c22059100c0c20000c100380c907071540b03001404604410001003180c100350389054a40c0b04a81c10440080c0300740b4007900301000004014101810302c1d2134296a50282090ba40c1101c0012401c000e000d43c0e1142540c2ca0301e45000c0c200348011090400c4c0d404030716002d1750009066150000b07201092100c0540c0f04003032941c054071824080708510f0082007001c00040c2d4003d451581306001003560070348400000c102c2504900c201501e00944400c0321070070790304034200613942c0400310f2400d0302c8846118103e0203c0087c0c0c803824490303041c40e010b40c00b03480042c1039030350a100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 672171052 1250 672169802 672169837
    0x20a0c0b0405071a19080c03060d020a030609034e020d06031407060c0b0f090f0a0305030105040506010e01020706200708060604140c0a051804020304050a0b1308 71
    0x20b00806101010281008400c0d0706502001d606240e0300d00d03070068900103608070001041c2d801440c4503404c4070740111081247c0c01d28540b0380760104894038400c11001e1f0390103c0717800d0300000010703c14800c0301c040b18400e8031800300c9400ca04c2c901070071640000c002d0400c294091001041251182e4440410f2003100a8191840c002030001c0d0f80c000380109804500c0041c904038011090000140b282c0341d810382844111000d06031102030442c7c820070010710003400f20ba03080e40810b01109200030350650052407036040f18003400b2100c40491404004c80c81c2600450710000062005041a001b86544441e081c280781e080c090415000030340d00c904610400040060303410b695050490b0014400ca0001c440c41d048410042c1c81e0985552221001e440c5036100f6458060590114201703852010700c500091541d0302e080801c02202503c15910100100c9100c5030505050f0030305543d1480554026030050b0010088a106440c060800c88400380030b03004c42c1c2d14218000c10005030b108084818a601102130000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 672172302 1250 672171052 672171061
    0x1d01032d020415230907020d1407020301110a0309050712050312070201110706140106110a030806030724110c2d101106011202062704020406050a02010e01020a0c0b 72
    0x1011a0103401c00c03591594882c050038100c403044c000014007084100d40e080c0c5183c4440d5002d981d6800403014078004261503038015240325484401400350203002034008203116500202c0005903920001c044030209680315a5981440000c00c00c0f000a000000e00100c0032444a07107803640c0c3d902403816402a000e90700b10009407460b20079040803201440c00e880d01910386110b4039041020300081070100807104100d000008650740b0644a0724003003081000a045409516101251002002800640c041c4a6110005a2003a807120344001c1c1034000106149800d003482001080040f0a144140242d0b105180b40c000603034500c3d01ca100340820140008810903030001516554860310000d1651140c40c0c02c0302034143c1c0360810720132a5401040030544445070380b00c1ca02403813140d2154001079040304051040e0300308000c0c11400f406100c100207450082481c815800a0142d0f4000d4001100195002c11040d14241d024081d080c8004607150081d4105049020000d2902c41500e2000d00303c41c803203070040b8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 672173552 1250 672172302 672172331
    0x70b12010b09030c040501091a040606230c0d1d03060c0d0207050715051201080d0203030a0216241401030b042a0603061503050424061d01032d0204 65
    0x1082134880640180b02a40e50303000910010030089080e0403004c20704200c0c45c001c500d494451a002c6d0303a140d40790010a03081c402c244240801c041d50030b000b00020100b118407c3d54004000001341410310359500e042d03400c090f40181e4985064000854003a0b4452018445c1c0c40d2078076402d07070302640c140c51030058448186081907490b01031594080c172490041c00110001e900e5000300242030240740040464010b0766603a0b02c59a403009488841c4005800a002148010f46d4580040280c0c904440c07452100001503100d0344025800b20140980903190101c03001926a441c1c0a4425080e154001d010003547c5540c0361080a400300408c02840c0b0700d80c0141007002d40345c0008488181010508000000b1502d4400c05030040c0428050300c0708500c1700000c01c074136030742c824020b480c440c0358452a4480305045034403400310000b601c0d0306112200c1d40c9480000c2901c102e000c5070410418030305400c0741199403550501c620f03001d181214241c407580c03c0740403403450080780d00f00c0343e031000f6410b03140040d130021501c814 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 672174802 1250 672173552 672173563
    0x1403060d030f12090b041103060f04060203070c1407090f0209030a08130f14011409011205190c050306132702011809020315400617070b12010b0903 65
    0x19005145403004130800e0190604403984a5841901c007a054100b4003820140e0322a000c98030468001c035803000040016146401568000c00e0134100070ba4640362941c0c40600c6403010b000c12520f40d6000041c100300c030f50070394014841001848442180783c5040d4002103a110580420054140d000000c1d001e00225040760781c14009081c80d2a80058080e11880c0e4665001410b00503d40003d0080080450448400301100c544200c141c6640100d100c4602e0381d503010308401130640e0140c17000603a15400c680b0b290b0045c80301e46503650340c0b4581c2e2407600000304081c0c0c10003042d90044007032410801d92002080000710054800d1260390380d41c41c280b010f00c01203841c100789020340c006a950780100000d032881182c02650081034420074801d00845007505111a046400d03071824140c1d07900030101c04040c080030001410080d01e49040c3d5052281d100029030542c0e0b0594030488800001014622030400e05000400c05000ca011006203082d1680d040314150450600550301c9111000a00007056502000b9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 672176052 1250 672174802 672174827
    0xc1e03300a1e0e1e070905061e120f0d1808030a17100302221a0f01050703050702040c0908060108031905030a020d0609060501031103160302031816061403060d030f 72
    0x2860250608000301034403000780d03100301e100303060804c80850032354541210a00344421701e0409200352020800304104240110200c00c640c140110008168010b030107000c00100c50344075131911040c8078541111030164440301c2d070042d90503401c00e10103060b00b540d010b05a41546a6400050040b80c0c0712440046445001ca40c0020f40c00200b507c4109a42d45040741d0b4055070300c512030410031901082d03200e10098405c080301c0299100310300031003090795036000d5070142c00300368081d03d040c50400045901050480d00402c15200118104c000c1c01c124050040007001e0161040001031400c21207010307603405002c05954103540510402000046202d42150b064649402c005042448420707034030039a542c01400640101d0340001c2c104200740b034071420a841203a0149500340391200f26a040318408400035000503142d00505030940751401840b89040010491101c1d41c081c500710355078980440a88041031141a910071880240f003000410364a140b04c44804a0f0903040000d11a4110001100c445030b038403c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 672177302 1250 672176052 672176083
    0xd050f06070816180509070212040b07050c1008132f031009030e0409080f030f010e13020f13111615020c1e03300a1e0e 53
    0x10009a140e2224400e4000c1d02d01c151452015288100c0880d01c00304000040c1e0804c260b504400c12031401c00101309a4010b0703c600c11b42e85070304291000002c0320b83c80380d480359645120125140041c00410b21003542d20040446d044240c4402014018002800c004d0080c0401000341d6914010300505014403020754400d02130700c94a0175034040c0101d11070007050803804c1c0a8818502c10002c91010380c400d41210940684a80c05e02c07411a00401c80074052040049541e124244400e02901082d83c001c0e5000345030003a1452450740c10f0014544220200420700a082100012110056155404544070501c800e65160a030400305a0040020301f541e41c4950341c1102c00021462920402080c80b00d1401e0310988030052502507405002040e400b50282d004025041201850020382110b8040f10300300c0d05210650b401c0c130070308040d12103c0f0200700c1c0e0310103820f5401e0107443d20b6420240c1060313a480742c10100c04101700302800d0b500c141b5040340c094100790060f698416080c170070b88040220642448100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 672178552 1250 672177302 672177313
    0x307080a02241009020306030c0d0c0e0a05041208060d0b09010606110105040c05062b0c1e02060703021b0105010305030712020708060a02090f040f0501180207110d050f 74
    0x1800c001c0d6288000a4800340c0810008a80071140b91102c030078034060406403201940850502c881c15000b0350002c0d0805c4d500d441645222030554440505140d0b03003d00901c81c40015500d80302c8d11516060b802040541024904002c21000880740c180ea071880d1091460416496541c2902081a640041c0800790062108000b04080c46030305421040a40d0800c0e900d000031001980c0486080c1c1e00c09440082c018105400306020a050060160420f503949000e40800014180103554500711a038007100c9006440d0004c2c201b06c0c6400c8030080720011018160080d042d6030f001d10003500c0e40e402400440030150002164442e05c0b2218480003000c1d00c0b988020030455949281c10f682d00c1e4050402280d042c549458428903072800440d03201b084a40e44006040c555413100001c40003540a5000d16500030355074908088152141c2c800e0f44100e50045e600020994180f0848410014100d04554149c5004201c5100043d180d480c540341d14803001d40d040d40e00000e0341d00e81542070001641c0c00b001c603407094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 672179802 1250 672178552 672178567
    0x3140d0e0f0c0105070c053601090e031e0d0b03100912021c200d02070501231614060408070c0909030516060f02070804050f061e03040203030708 64
    0x118041100c035074039004451600d100080192158000d550000d000c440502d001001242400c0c400240c00a61882070402006c0060386075210b036646a240c41141c0b02c54540050103d07002d83e22a8465a201d190015400c19079000110032000d081080c1540ca140d0011804001003a819080701c515160014103544c04058006400401007079200d00603611040c440940c500d40b64004103040b00761a01e00513050400c201c0224086d0350341c1110010001d40340300d40e03002901c2c03100014001c0380e050f5080c56028003010340c0341c40001804412010551030f2000345c12090300e41800c25a90468007550809503070300e21500354605101400e5000e608900500d0700a07041040200801c050007880c803a881500061005c030385414802080b616a0318009021900410035041ca080440d140d0820f0300f40300d10004140c01d907100100200360b03041900c088031402400b02d028822464034088100200c4802d40e20b590508030140306200c40596289220032038070700000045800d648060084843d020380018105070380c0c098 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 672181052 1250 672179802 672179831
    0x4060b03011506053f09030702040903030b091605042106180311010b131505031603060e0610060f11010c0809010b0d080306040c030603020904050a2d03140d 69
    0xc40310203507000086030b4060030103048981d4420341c8001e041d034608519503841d2807403641d80b1702400b02c00c0d85100601c00d2100503690f502407000b4480c420380d80403424000280074012410000f0700320f16002c03d052001211510381c40003c2d81e003110032480d030041142540003c1810008100000580090705010005280701100e1800e006814440c0d03550b0800883c2c0c0702c40032403c840c0c18040c01c6038014508010710603802410f420078006120fa0100c5a1481c0b9034600029180c29990090b042020010210400503c440340c499886503100d044003034000f40c903054584050066007401018144184940c0f6204038a2094041081c0100400020007034042180405055000101d5643c1404c0d800c2c030030782d2003107800c04081510a065004100b1401c68803150304010150019000550816a0340c0c0c0000000d83d6800364118021801000a03007102070940c100703c096a101c6400c0c4106001c02c80400c0302110301d0030000b40c4a441c0d05441d001c80c0d8010b41c890310906c0d82c8242c05150000c2c50030038980068696 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 672182302 1250 672181052 672181057
    0x150409050c0405120a051207021908100b04020322080d0e010f06080a03080601030b12070b071b0609030605100b031e0106020a03081b07050a050604020102060f010e04060b0301150605 80
    0x20030803944c41c15441c8a041025944045d220401041c5070090000c407840f20b01038130054a8698802020740c4183c1e04203090304070303200c00e255001040d550b000004040e01103210348288038030a4010384d4194039603e0101c44100503042504450f8080c503841100e240e00780601c04080d03e011880030101844980006508640603214006001111900d03200300001c55000000791656001d900d61500c8c1c072180e0314000158006d00c9400c0c14207401032214105000000f01c00e010380000342c0f165464698640b455420300f1a030049040c80c1c11445845c0501e800d2041d580c028a184044035409030f00031447d40d4822600d265014255031042c41800c40220900c990040e440b003040c0c1524003a02a0718134035a90700d4030226a81c5096a8011303000c10041008038886142c0891510030f001202c10080b4075000c142c1d03507040e181040c00c680550350303904020188021907a06109041d00034400d2a100c5001d541031903c4000321300f1000c0c0000300429510030756403056803400e4129178045809120303d50300c1195034810141450307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 672183552 1250 672182302 672182309
    0x12160c0f0e060103050906070c0503130608011a0403030c1401090f0302030c0f01061a090a050d03121a130c0201270605061c0b0403020c0d080a110105070e150409050c04 74
    0x4a0301c100010310154400d1003000d200e001000014442601d8003402650340c00b4080c0410307145170104000303035a0300301003010a02008160b15518400c803985001715042c900700d05441114000841040201701007944080c11003580780d001000d802e0340445540380c09005020303c03100184407034001040c940c00d01d500800076124244210040d6000070180c0103849003221501c0c02400401b00d04240050500078070b043c041c1002810107858040309589410008401010010f001c50009041c0e14411028084134000c00d44a015084d55514000304004006070f028000303802d0016105a5403402e210300b851003504240d65048080d0000054183c810301c00a401240c5040184c5a181c2420041112420328822441c0b410b030b00d41802100c81c0d142c0da903581c0e00c03142c0050000d6003103110f48032815590383c1e01e00c4c0805885034400d4400380d0303031041a2039002d4400c070300100062010743d242800b0055069000707400065141000c8445031401e0203e800404221300403500f111108500d0501042040f407400d90081068 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 672184802 1250 672183552 672183569
    0x9040b0c1309020423010f0c06140a05100603200706140906070f0206010302090402060a090b030a02120109140a1107061107020102070b0304030f180302031b0a0506090312160c0f 78
    0x1140d0302d00b090b0f0303404061740080074009448480241d400510402e03032070500d41e1041c1e80101d10306c101030121082c1e8400540d906e1a20a07650403d109099582101610061010f820144039807200c0500c00070520f04030320124103a0007000502c0c81c0c20003e25500c5200c072038600300d1410a00d420051500c1d51780780411038154021070004141151014000541c180c1280d034010580301c4c0f5640c455003800002d401c03425074072013842011040400c5000c1d02c900078500c179065911006880d541d603802206808241030740b008004902d40041d0000c481003400710180d20020001001c1007010b40c404124159120b0030300c0150410740383c03014038030714400c6d50b20040009a000341d0856403407544404042074184416a0000c0100d0340782803100405500071450203070014036001c3d02c108007a6990f00400d00f490400340b128501c54078070701c3c15042c0718a88a52518050442a80e01d6400c000414000c60740d02c1d2400900341100d4100440d00c20185242d100141058640c050700360416070b5501c0941010903280c6018603800e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 672186052 1250 672184802 672184829
    0x5100306050f03070f181d1501060825050c0304060503060a090b0108070305070e222f07080417060403030b03190618080a0e010e04060509040b0c13090204 68
    0x41c920f0001644c400b03841450701e401c0c0186250404070480c0d82000c05503000038603160201d2250f40100b41c40c00c0c6000c0c1d01d156001d01802c40c0b2200c0c0088176680160041d405012200b010300c80c40722072124500c110f118030081031981d006151141501c55000380ba0f80b1740b00701c0c0700000780841c0c4a175110018500510742501c8045075940c4a400300c80945503101c0c40ca0380012003c5001504080c400d0b08895001080c0c0d0900f140e0101400e40801c1e580848803e10915031103400c080201c0700c0c146407240410000b81410703c17006002040da0900909503c2d681018440540440d01c601849404000c84000f8810900e02c0b9000135404c00381c103525108101c5099000c0307480c00c07440703000030b0501107015000b000c00007030300c000700c0902070f502d000040040726500b59074291050100c0001484840c0101602d03c0161140c2022000c1940014207041c144580c0d1805036041c5a810080c03600c44507100b40d0420350004000b003095403450003608003806103210041400d5465a0009030a811079401031007a01c410107140318 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 672187302 1250 672186052 672186079
    0xa11030705030f0d0905060a020306101427041506081f0306051305012c0309031005090f0a0c0f0605030f0a05070302071a151203030c0a090510030605 66
    0x1a2240121600a08103420800075501d222112a0042c280d201c0080300024201c00203441e46450b0850460758041c3ca16800418030109151800e1000602280f034500901c41c00b01b16001c5200500a01e15020380301440c11803043d10b5402800b000106155000c0c10800c0034142a492901000c2d0003407103030401080d2807001041a0440360605100c1041c3c0c07121105c0c1c01c04c3d1441e60741c5002480e00421054a61070382e044a000005ea00707009015000d44030762280c44004080c0e09011850101607020b5290f5640704000c64880380e1400b288202010f16004030008d141e644510845060242c600140040e900860340e0700e10800c201c20a0a009440916814031412915202c00742ca4500c000d862149181151100040030b60700300b40c01c01035010400741390150614a1581c1c4802c034007260294044d0140c40403c08210303009002c418601030a0750110780c45c0600c0002d40c03070140d40702d2102924080001034000b132040e81c82809018488000c24001e1304200b860840701e07400070000c1c010340c014988201d500303100c0c06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 672188552 1250 672187302 672187337
    0xa1a070305010f0f06140c100b0906030703110d050109050316050d08040503090d1b0f051315030308100f0305060f1f050f0d0506101401031b051c0507050a 68
    0x81680e40071005030862900b00041030300e10b0324a981c0406c00748901041002c26124090062a000c0c010001001c5544101e8070100950300100a1a640c0070b41d10003078041002c0740420b4143c005000b41a188803020f03000500300240034101001c1c0c090940e10002800c0c00441541c1c00c40180d0550150090381d083d03440a40086414007400e49001c0c1c05903105102c2d03040245001070500002034400d0445e2100071000514804030000c080d80950b803584810403040010303040040503a0301a590441e001c01110200c5800891942c009000c081d040044180008880d4450944c4150181c0202180c4000c40c95480c80d1a5070b0f070350710443e0001564235241000c258120744804410003000e03103c2d15510a410700704420700c0741c00b04808900a901c41c44e00165203011036824005030f4000c0c50081c00075115903080032907001500c1944072840303040601c3c1030391032105400701b903070551841d41c064a070283e9220044a001d000c240900404038281718503010900640f244c011004210800d0035446040d0b60f2030050584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 672189802 1250 672188552 672188579
    0x110706020c0a050910081002041701020429040e0c0a111f0e100603030c0c0b04050a1403100c021c1e0e180a022110170a1a07030501 58
    0x1042d4005440b00014005440c00b040303003030740c810b55121908071100d6071503881910304000c6034240c1031003c4e130000e03080c4482e5164004c0019400181070007585040d203411040c45881040540062075018240c01c1c550300c2d45003242c1114002c2c040c4107614015030800c103400e01c3d21688041407500200710f90f2a80b2643c02030380490200c91301c1403080001d80306441001c944602900341d41c042c0d5181405801c2c0e10481700c2c065881044017450084d50f410742c00151601c2c141c0c8081e4a281c0200c0d02190f000c0c40208599900e40c0000419656442040030801d022030000c039141c101c8580b6052742c1c083c24058001c01959001030754507180e8000c0001003208a103501030548641d0741003c0788801e81240c8101000c1c2e80d80c02020048042c450242038807203250b00c1c641550000c004180c80030005181c0000300c1081111007005013004542408800649608000c403041d4400381e0b07107202c0d42890044c60450040310000501641c2c4266410484044d00b00441051002104104a4041021074546000800da82d24490325 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 672191052 1250 672189802 672189823
    0x4060204090b1818070b0c28050307030c0c0b071520030105040b0a050a08010c09050609010f0e0f0d03080615040f06050c070f0603020a120507020d030207021c0311070602 75
    0x340d0b603c1e8581010600000b50068091600b80c13054103000188451800003c0100402881c0941010359202e940100c0354584400c0744041901d0780c05030a80443c4010084490059040c14003d0000c90030b45841861114240e0100345c10360b0300807e400c401c3c841d8003030348500c1602c6442c400308403840c020082000105d403c020030220300c00e070910040c07166003007540c407503030080b20000d0020702040d6a6400150240e005a0400d4800e65142c0c5110f00780c3d25081044140036000803036141d0304004819000030303c0c1e058240000f0302048000b4503901070759180c0e080070b42a00301c00a4090744014556080c06404880f003590300038040d111000784d100b664000003040c0c90a652700320316204005c600d80403044490740c00046414541e07000f1440002411184040a50014440707070310003503114400d030725015001c4610401e00c40b00b403500705000c0145003a8049001c0100040070300700181c403a0014000704d03800911200e03604070118061060641896088070011411031441c07002c85098503100d0304101d0300c40f040d084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 672192302 1250 672191052 672191089
    0x10b010212160f020d080f040e1501270906081b090c031816142815021606030605090a02041203120917031e09060121080304060204090b 60
    0x100c010000901a031403c05000780020702a0785030210503140c1e42d00c542d002d8072008040c0c0f580040d080201102d11900164015401240032000c14903c1c1c0002c0c201303100c107030030b2400d5041c04030381c881e030481c24655901400350001c00c408118981d141c002c016a40c0000c0b10049952000390380c00b42d100c0b07280a107d15071003000d880740748900b50f4491400407042c4081c04041d0003810302488850550342c800b2285000d00415801604501d400801001d03c800140031090303080b5403120014180f003c80100341e0544045450442c00d0056010114500700d0814441c10001d099144404000191980d4543c1215094400486145085450b0f1550107012031090b40301e5041408103900706140171030701800d1340201d020344c10364000c00c03e4043c4e961030300b0302104032400c102098800030040c05000c083c584440801400a040d0304035040c1450050b81c2e035584414810168a04003030012408035011068003203a5055100980c80e459007050302d000006508903014100c10140781440785c1050f031404c001488c1c80c0d1807118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 672193552 1250 672192302 672192337
    0x41a03010f291204030801050607050c01110a0507030b0702010b3c090702011d150c07081b0d030f020405091302190b090a1e121e05010b010212 63
    0x16104081e0203081407112907002412041d0380880090320040041900322000703604603203010701d0040c001c46c8042e041140900410300082c000203000184228180b0400d003070031030200300852100d52500300313105e500514601070104d00204209504807018094041074000f400036013079540034051a61a030441c0b4000b000b558414007810900080c0c1c14444070300e14400c0204040c1d2910b404125200700c15500e5030010703035403150b00810200040c20b41f0b40301d900961001c3c01181c1c4841d6002d0b880054098001200f000f00066160308000011007200c0185c44112140d602e10162401490344803102c84140c44003080c244000884280141d1080340c007519001410100c698031600000c000c28980c0046c12a0010f14056080715020107581b0644003d21142c1d240a5650022100784100c1220300c0e4001c0c10b900d148008180780c4139550050200564540c17590301200113109090102d0710710b811079134803807451850b0201c2001780130043d08031030582c100a03000c83c0d1500300c810001078620700c00e40700700d8085803c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 672194802 1250 672193552 672193559
    0x17060c0a0903120e04151a030a0f061d061f03050702011e09020f0402070203190812010f0905090607020c010e03030405040507181403030a08130512041a03010f 70
    0x1a04090162920507240c01031680d81c50740d6440d900d6120040c84100450762510310010940350034011150300104e000c280b150034600e4038040d07884880750280321040b9008040700094410b00c0da03601101e03021202c034406201c055034828050304d990004209400e81d80d0b402c00b001485509281204050b0301c640d03001c91140742d54025a08070010302000d48004119520343d1010802c0340303166030605036031202c00b0600080c070035106d05c10804200148003047e8001c3c0e006014010160b039001c50381c01640600e004002c80d0b01d100358909001e0900c07540d400a840c01c1d86c0d02001003091903090041d003056a802560400803500e690201a50b12039080f243c184c0107034085400b210301940b240034000b5800c10043c007280d0a268440c40080c041e2202122090001418490025445400c601021b130051141000c41800c0e0141100170984912841d001441403105c82c801003141c3c400c0780002041c045801800350795119506040c100101c0d8400d210b49412051005180c4075110448404c5034102d8502540c160708452030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 672196052 1250 672194802 672194821
    0x140a08070605130209010e070e01110304051c080304080301090b011b080a0c08190e010c110913060519051509180f06040c050118060e0906120f161706 66
    0x100200201c400f103424055120050701c448041c14040d045c0900c0454092405000040170200c122008504110510b13190310b446000c040200c8040d1002995211a110b507200c00d2804945040500203000e01000000c000610174000040c42c10b841c9443d04c203100c458094001140d484225560040c402c8540b0fa0703d81d0b00141d01000240460000f46c2000c220150071501c8a22154016030b2103003070022a4940c0c1d101f41d00f03074030003c0d8481d1a44c1c24200040c842c1416105c1100c17201c2c2d91003a0314014544000420749035000940300461241e03228a0511036840d04210541410f000010b144c1003180c00c01001c240082000c89980354070110180040042d5620040266025201600500c0990150040a10b40704e401840f840c5e1080f805848a40d044901e000700040912091100c2d03103d902c43d5041050203200d500241c44401c074807040701ca00c0125100d4070005420381240000303540d40d510607001600010b0501042940700d40041d504503032140c0d030f564803078002c240080044032607254020000240342d424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 672197302 1250 672196052 672196061
    0x121b08030a2406020f10050106091a120405010b0a05060a0e0105030402120a0c0305101e09240b040b120a0b0405010b090c22260307150603140a080706 66
    0x380d000508840c20b00103002821804800b42e0420401030700b03c440400e000483c01c000b014514036400304108025071405800034261109805461410300001c00908210015442034440d210b406100740c002d07034105450894000d10800c0803450150410400001e041e03e0f10001b5580c0d258200c1e00c642c07201c05035100c0111000c2d403000f08100d0703110aa525280341d07075500400c100400c261240714100e5405045042461404010707066280b280c600f0802210315005020680200d07003294014046919801403415094030141c140b540c02900348602c4d59031070040d003e0381158100c11010b41e0104030241c460003d00c01d000d0b424040d1041c50b0351010416400041e40d207000c542d03115004900006c1c0b030400c1c21001900102c0c0640b1502c5124401240452940c0d071314160100300f545042005075942480c1010a56a5103400c2218103280c48003c504072221282c14000c131401d075580003605041541960642a000f02404d0009903020030740c4540050004a00140c85900307290056a000d0030700340150b03950005003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 672198552 1250 672197302 672197321
    0x14030f040e01171203011203090b0414030f07140904030c1a070f08010b0301060c0f08070807062a140d15062c041a090709031704030b16050c0a121b08030a 68
    0x8427020900044083c0c140001c1c001814010343c10110942008003050300c2c024030110349002c1e940244100308480400c604000080c118103540384089503845084c00e9440a04010008e054410b000d05c035003d815011000c220f2140c0c01d01d071122031555060076800c0300c0b454000d0040d800c05140820044c0b104900034102c2006e55407142c420754070140700340c0c1e50b4100c16030800319007200c0c2500f021807004200b001901500b0043c03510000c1a40200c0c10020060b0364048900c82228240404500071340101c035801c07004c580020041590902c1000005600326100380d070b4501c80c00002400c400072020f5201e518040300c00f016110146024581950201000010104090000d103101e901504809140d03c4007182c00348100402d80712040c6161031418400c1080301341e84c140c64030490080000b44005004c00f44c1c070030303000710b090b60903208078251043d0156024420303154020140d10030a40c00c03500300507240c441c0402030700b0680d07210300c40309004407016040075000f0703240145884014030018210781029030001c4d061 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 672199802 1250 672198552 672198557
    0x130c0f0b22050d0803100e07020c0118050a0e18010506010203070602252109081f0905030f1305030d09030b06040b061303051209090414030f040e01171203011203 71
    0x541d5030b03000411002c421031007160041c02c040100118903c001d4000402000c1075100c4810924100c0310007901c860310580d12034188440c6040e000c2c0f83c2140c0e10141c4000d40000340448604035159005481c50603004c65614407400841041401d1401c418000c0328082c81c01a0029401c1000070b40c3c50502940205810340f06405980021200722100d0105860400340942c52007805522800310414200d45203080c034805200c41210108845800051784142c00c480c1d060740f0b107400c244442e0424014041c101d0000d4481d21022421004400c01c0f0720060504103402c1c200e4080300c1b60f4850134136865406440500010034848841000442c200c10aaa60f100d100184009a9504004001400c542005002c02006000450b040c420032004221401a2240c1d402c41c00341045200d000280101c0801000201212881800011b21003001c1081e01c80182c1504449521507445851107807015000f44100b405004001c083c0b000030340310104250315039040001d03510707107180c0c00d08500c0c08001c4030981d0100c08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 672201052 1250 672199802 672199867
    0xa2a060c050a060510060f030603052508071413050f18030c06090705270109110f03070507021c0510020a021204080c03010606170609040218130c0f0b 66
    0x503c1d2403180f90301c5800a624194074481c103203080141140c80c02261071040c503103032030b2040c401700341d0001c1e0b003c0003440032425000401703041d0305010744101c1b110741c040d030094801c451010400f04200591820003000940b4201c1310580d00840c18001c1e40c0007924000c04101728040491494200700c0a5040c40c40c4081c01200c0c5000101b00c0c10700c0c5400d0088441c2c044642003e10180414039144801c0d4001d0381035050310401440144030781b90340a80062090b280203075911500c00c0310702d2000d0400d440b00804600c40b416280d103030041003e0840d500650b0100d12a54404000304580c140b4103041c1d1640e01e42290040149041906525000354001e2030003030103520130542c040303c00d480d1550080c8050728940c00035101580d6900145800d4035110342051081c0840d2915802c200e00c0131121144d03000c0e41c00c80300c00c00203440390b00108107568800301940e650303403400e001004448a07200121060503071146600d1210150b0b107000b2120f64031014020301d0000b410030031105a91302050642c015641d02c030b164002d00b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 672202302 1250 672201052 672201073
    0x13081b06190c1a070f030f020c070b0702031203070e0f0406080a1203110c0127031403101211130b010e04110c010501031a07030b0901060f0c0210020a2a060c05 70
    0x42c00e0f810116010b90000f503e1601c8504869414000c140c004a1921001d60070a0741018031942c551b04a0f0150048240300030845000b5590b040090314520211107181554908081100601e1501064401c13401102d2105c0610364030b003810f01c80d140031584c10402404090326a640c038146058044101e0300b08042d02c030781c1580920b000c158000c00c0c50507145800040e80104508002c030033085441000714a0b4071507500070902094210303911402c1d030000d1031480c82d500d94904400020840c0603800031001e0701a000e00c00c504202d01c10909158406088400c1810b41040039007140c19165240702080c0015014940c081d010309143d0440081100811012070418056240c05421070380243e0050b82d058628900d580034030310111804039002505031a09001001c1c40d180801c01c0c9605c10b01c540c60800c15980d154160062094034183c000544c02090340034040c1c0c1401000350754040360201514003014294600e2001980816a81ca2a110242410100b81c0c030740802642e0300d00d40540c05946d503009520380346 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 672203552 1250 672202302 672202343
    0x606051c020f180114030c0a05100537030e07031e0f02030a060605240315030a060f020a140405030604080a0c1a100603090302070b030a0213081b06190c 67
    0x81e400380641410380d01c482c170854810549002d855501841c050403124005001c55144e109003080c01900b24241181e5034441d031100c0c02034210038800151141200d0380403104840d513002840003603140541d5800d000d1480d10101103612921a0312008284204005242d004858000c50496649005660f0f0b54400c00c0260040303030034180c441c4801c69146030b8410040c0054503180d040c805e813030303011181d00d014100c100300000300c003d12000e410010101101c03003c62456580c100009522558404814010042510501e001070340042c040b19012907240c11105203031444da101a2421500f004004001ca40c54980b5000e29039441107040c0d104000e600020b12000c501d803441c0c0701c04414842600880ea0b45440a610060456540c014104140c240703250980826030020340d00054401128001e030307623911607800d01d100920070114840ba041e059504001100000807039205074002c82807000c0c0c101809036100f00a2140300d002601d42c0b0414111040340c0c1091b20503086400158414002d2654a060702c6009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 672204802 1250 672203552 672203599
    0x140903030d021216020303040f11100c03080c070f06180b0907050108250806030717011b1b0f03170c0d15080703240204060c0606051c020f 61
    0x4902038002030140c1d0614241508143e0013406071102c1a4402c000e07060080d12413001800180000c00c604841009011104418040d0f80354002c11003c00d0002d4035002a240020004050b4082010703400000c82780b40f524821038401961003401a06005403580d21200203107000080001c03c0b21501071a007002400100c032841c0203130550401081030b10701e0300000401502c40103090144540080d03030581200200200c50340140201350404010660b110804285407180a500c01028140d0621540c6441c50040d4004c0302c0340d039144845028a1002e01c40181e0320101400b10702d41c50400c1a03c01e08010411a60514980c40d1080c0751200c550781d42c152010446080503aa0107001400010700810603844134487c0a201e40103124020500350315214005850b10b8072840090140a02c1c00046001134002d0280503601140c103102c11501c075902e458000303080d2241d0750001c4072030610389400072901d841c1012071440c651026450044020b00c19a0074000180c024901c03158022085404041c05642080300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 672206052 1250 672204802 672204817
    0x80903190b0109020406050301090c3005160c0305030a110406030c120921030209180403020d0201090c090e030706090503091c0f06020306030f0f0a02210c0114090303 73
    0x1015101803080d400d040c401008107070701c00121140304100800c40c403500038003034038112050400c1c00524480c503403138162011050100054482c42d00b04e042c1d4a280b920005111440c02d0160313808003c550b881a00301c02d000091b01882d080429143c1d4079030000a40308600559200403c0503009c034501c94401d40024003034025400c07003c0466168480c4940a642c0035044028451400740300740082c25040c0c0750b03114001d0b10000100a1030b110b00c0d58040c00d081c002d4040390b9402c080640403410102c10b28114482c00501030b94124014014510103400846c0305006141034181c10105128101e85030410f8400203100720140c01955010900240c8049841486a00d102a009102440d0348207043c8081100390b0845090b003030300454081e000c1c0303000309000b080340b092600d0b842500180d8030748800c40040e181180d9003442044038443c59070310a01710031010a1000361103100b610070f10300701c1081910000b00e000302c4210303038034107540040348010702984607080c0c0c4244405880d078140c0c51701b185200881c0c2150720296 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 672207302 1250 672206052 672206083
    0x10209150a1b0f0b090a020d02040e010b12010e0c03340302031005011e0b072a060c050d09080c150d060603020309070519091e050411010e090105011b080903 69
    0xf040c20600c014030702041e92010f00400544101140d41c0d001400300100104080d0184d55541c500f901c04840035403010135000001010700302c08618103010203010f0440400300342800d00134014542c4e194140012100b0955881030400114204109000300859100440b00b01200201d07a000202607141844894003080b140320010a0b01c0d8101a4500a101c031900000d5104c0b81e50382c01d0400040304004103488a080d40a01e900f0700c0700000c0da07a0030903600c2c85c818419100740c0d8140c000189007500000d2450f6094410020354140248501081e51000a9407283c0c200725040214a810240b40640c1048a42885200840c0c1005003179071000048070032030b030801c402099000040c0500d00c00c7c00c200f04d4004041c1101c61240d01d0f000309601c6080714146200701c84010b070b201c1c00c0e0100000300e603c08001c14211110303010000d510f0203090106c030656810714128081075459894140b24203041d4042d605a502c10384609038000b40c42800c000003c0011b80050351144010300c80070119070380130b00450b04101d4809 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 672208552 1250 672207302 672207323
    0xd230c06180406050603090a031d1203130f0e01050d0501110c0c010806030a0812040309050603070309060506150f0702030703050a0309180c210212180d02010209150a1b 74
    0x201c00b8803007114103540220344103031024010403800c03010005004407626414542000d1145440b502d0b625141c200c01c901503804150009210701d441400005410481e80074000110000ea4400150341c1d0f4444602a0040b407245820043c021801d01000c14004948a2000010891604041005190003081d08030030310b600000208502503074003900b03480c0c024200300d028250180499071741c3c0c00c030f030310070002c031081c001c5010703800a804d15005070901c8004040c0904000d03038130315140d40010024240880308079080c91501e0041404c50070210b041c40300c01100c10240d2840e00101003507148164220120880e4544600d00740840020810302c60380102500c80d4407042007140c14000c004800310510b0714403008051070030800805850344184480c02c80c00707030a0300c1c4044040110344400081d11412001c4100a072000c41803003504005840c601243c0344548045e00c054640c140012401c0c1e10035400381990103660303049820809920300c001403400e0292803d0403030390b050205181510360305049a0a030b0305059413 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 672209802 1250 672208552 672208597
    0xa1716020f010e030304060b06370e0904060f0b03070e0108010e0307120507150c11010b04020f070b06060c0d051801081608040507050303070c03060b0d230c06 70
    0x10401c100c1c041007050020320800021a280650b28000184090400740e111002c81e9120349840e400c48404006ea0b50750002d030112030307500d8000d5401030369540c01a064404460454050310031060081030880040c00171005484546992001c1e000c10455418815030b66003100c00d6507a810810310008140308400142150314000e415821200d06c1c40b03d40d01c264004000f620300094458001035010b81130741c10120b407107182500b480300c640750a218020b5001407508112074069034212903100e00c4e40c040c042c002c1c04804028801d020690140c0c245102d0400d00038411100011005108280d224201034405410100440c110b140b40c42c811444003800326000041c0000d01d0b000300c0441140f14142070074141803130700f40f0000140c50505210958002c0000744001b117420800140280b800609000b021a6210a140d0134440025041c2d48001c84030545442070360fa000f41009004001d005411a00402c01c40032600c03001000c00f03192000c003100d140161041446640d8a00c0c000d810254100c4454000d5000d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 672211052 1250 672209802 672209807
    0x306050402150c0312041106030702160b04080c0402030405012703090e0402010c12022a03011415010c0804090c03091101080906130c0506211503120a1716 68
    0x1103141d0041c4a14000f0066118680e0000085480c20342110b1040e51042d81c1e6400c1c070728182220342400d071f60f128a00006001d8030300d90006007030054083e00003c1001079540ea008000c5988114842e02e5110f80041ea8844510300c0c1c141c1c091a407081c020f000104480c41c501d12414441e5242c1da03440400c6c61a100840b03070525a0003a01e0b103025000908104610381481e800181449100c02001040012480e0310011164800d03c03201e441d070600d00b660300c600001004010341c121511040310b207001b0340c0382810031030455606000b540d0084400b402e03150039600ea11030044442144022099031803c400b000001401840380c420034000b60300c984c0e00082d00512900d0110404941c2a840074100030880c01400710740d0b4400300c0d01940080240b801d11108013142d00c0e0103081480664813080c0d201d5008140141f0f0021aa5000c50410f9820b45440506965086211019160700c0c2d00450300341d84410307002c0140d108100d0007041c0324170700d80c00c1040303001d80903d90031b101c145021121804030101700c4204500464 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 672212302 1250 672211052 672211069
    0x150e010305061807141c050111090f0a1a070206070b010f152f0a020301021c0b03060c09090c0408030a0906030f0b1c02040b030307031e080c180402040f0306050402 72
    0x6141d004d0185207140c034907000351105070a5185440b44091a00050111004c1000740d12010752000007400b00303d061180d012070701e400a010701802400d55030346201c11494110f0481c3c3c117071040000c100070b035902c0d00d030035100305504002c10480c0c00c900e0401405011518068016000342030000d40c201540707080100b82181c404c13510300848c4c20f00001e0000d08541020407103030710701c4180c10440540781d07400f21020102d01d400316201011f50954400a44c05c0d851003030000048400124280d0288030100501e801d042e0394020444001c41d0860003030011003603514010640c0ca8110244c7c4e940603040540b101c940e01c3c1594850800003000c82c40c085e10421100f80c01d030140590140609004204842034900441e04828003003a1003814111003000d00011503a459000c0f04c091800681140c7d10740015183c060700c10b24400c01d0010000c1075501d01500802c2c42030034030902c14400c0401042c1008000c45020b0701c1d5092003001c1503400781e000d100200300d20030100550002180601804102418103005000000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 672213552 1250 672212302 672212341
    0x215040909210215090111271f080901020d14100e010b040504020d14310206160c0e070315050307030507230405040b0717070909150e01030506 63
    0x950609401070401500030071343e042c02c1c0c0c9040d051a0305a40c1d0f5442c100e03004007042d0903408103405021820113180c02030301c03007545c10a41ea40c207540c00b0341d0040c1070300f04600141404428841800b24964107004684202c041030740140d029400503091050308510300007642d200c41c040c0b110240c01c43c410806440021180a80101000204c074034195061024006940c8901e02a50340103c2e0005844040306103907130300080024800f00c8050b9410b041c009500019540c2c00b0301d41c1016696980d9040c98440e6091449940b020350041c00140360004000611180e0042110203440c3c0c0400c2c5500003901a0348110880d2181e000727560700107414000002d11074030400315908614020382c00514240002440000c252007079806007080c2025201243c200f41000d02e581c0c2c0f0700542c210341003405010801181c5802c45010b900d46848101c030034120018071003c000700c1102e64a0000d264080700700b00074a2103501881d1185c07002c2c8160720b04d4075100e40301c60a4803082070f401211294850410807200c103040c3c00803800031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 672214802 1250 672213552 672213593
    0x1b05030d080610080723130e010f06020106080c04052232070603050912070f020f06160602161703011a07080307050a05091305010e06010302090307030b040215040909 73
    0x40c0c02c104c10006e200c0202205080c1c600d10301c042c00c04000b4a00381042d606001c0190008854086d211b80c20540e0f031031800c0c414100450301c000c20104180c0e0048c0a806d0030340387c82d0401040c810982204002c0507103c05042403010790904500202200d10030b60038400001d020f06600340010550450081114004581e860303249141d0800c1108508404a1403004480c443d02d404034181d1604118242081242000c64400700f400080e18010010042d03640d14846008984184a076801e03c000e004541c030900030030b060b07c515000700c960001406640030300319880d0b03c00c0004001c2d5080b0b944440c030b00301d5005801c51540074040010401c144007540c41d01c11011241e0303545030038540c641d9114140b501001c0e101c20700340400881d48400d428800c90aa480c004801049404010754140d0008001c0500f800f403c0d11041400c00003072180d5000c0c1c001c441e08118041c000b04011455521844018080035004aa000340f10340d02c0e00803480160f201400c00380c001c154000039210704918044880d00c0d80714840b03410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 672216052 1250 672214802 672214817
    0xf0d0908010911040e0c0d0317010b040e180708100207060506060f0a2616030e0c0d03030902040609050c0310080c0f0108040f020909010e0106090b0a031b05030d080610 74
    0x143e02280101c107002e4252004114010700e5042c0f1030800d401e0b0b466142c0c00c0941d4140650501d0303400a1074002ca0101a0640501c4d40d80310007295815105034019036540d80d507688040380340401886980c4d18100060130a0700c410a03201c0e004c10f81800d03640a1002d01c1c51f0b8010800384c0138130078203200310350f0403500803246d10780380044078450900640070b41d040000c00c1c00311200c1085900410014050084141044000581d00c0c00c18842e802030188107a8800011345480ca00c070500d0400091080030119000305004503c0303080c0ea8088014100301c0404036003090705c40d01d00142583d100d0244e0b502070f5425005850701c5c1d01e00001c10604030361a50380110b10580c030075a500c0c140c03030300c0303646095820034402e01e000c0714a6591424899400140b0001c029041203050080221341041984000224580440284680c6540d42081802e5889500d1010341c41080b07500c0400024142003444907035aa002d00748800c1096407040000d04248080c0222000b10720018104034043c134040042c40b01a2805082514 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 672217302 1250 672216052 672216071
    0xc0201172a070308240d0f03020d02072d0801020309010605031510030f05010e0f07050a120b010621020a02060601030540020d0620030c0d05040809030f0d090801 71
    0x2824080043c0030360589045c0203050160040114002810326000a080c24010a45500d00602c2099601c4000da0041c000c03150fa10010b1440407480c0f0044401c019480c80c60b0072000e070f100c0d8074035a0010000c850483c003007080009000764280050b5100c0e0320510000290246804240760a105954403c4030702903105808100006402035900b00507a9040000c0000314141d524005004260ba00300a074038134812419070400080000400e64182c030030503219140c800f5552080c00301411003500c801003928910400522105108803001c42281c4001c8040204100c180380d5004120f0f480900030f6401a0071900411200f96014044d10f50003514482c4087d082d500d41402200603606001c0c8bc402c440c200c0e028004081e9440b009d00da1280070303001408034500160034502800202894a032003034960307118106402c080390368501624400c02013184010b01c0c021100c80804000e090081003114001c40501580f07109445c1004030740c03d416494401002c0040c00c5031400380010901c0d92107800345030306220030f52 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 672218552 1250 672217302 672217307
    0x5011d01080d1e03020f070b010f0b070f060c02150103140c090103080a180b0d09061107120e01050d09061406100c0303020d020d150e0c03160c0201172a0703 69
    0x44a03d01d86222800d05140d941c0e10741240a813040ea800d103015100301082050030701c80c80c0344c01c59040320094400c0c00c0a40d60341e4005103c56000704603000e459202841c06100c01b143c407681003100301184a1060b150000c1484402c881c400b08280c005503180c49041e031100c1da41200c2004240d40d6184211400002585103982d910703418031070301c90303103034200b01c5020207400c0405402000d54000d089034201040d00d64081647c680003c0034120421b070b42ca81d060109915454918904844480c2c0d00702c603040c018140444815a680111140c440e8100074007003054108070001c0b4440e070a507562203203201107107510491007100003a0074003402103440b421244521000082e00b20700c00d900341c690b040c2005622a0350550b442d00c001d00420340c1c19510075003810b41601d1145444130500050316040c085803101516500c84014070740c0422500550403400741e000300000d680c0204041e040244c4140740581d039400c1420307451401e80d038042d40c1d8242120341e105c1c410280c07413202811640c1403650f104841414226280c400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 672219802 1250 672218552 672218567
    0x90310061707120c050d06271a0c041a0702060a0f030b0901180f09170301032906010c020f03151603152912100b030402090105040f020d05011d01080d 66
    0x51304d10031444191b25100300003040d04507000c109290142421840640d15201c08100e40d501011141a17048032003c84600b85544da0290140144503a49410581441802c0c0041c100d40410b1031280300060000900594803480142040209540da07138140020321100034042c1c0b100031400c0341c4203c3c461070042c007080c4080410312011159615001c590707803071555020b000400d0b83c540083d0410000d80454080000400000c5040700d116000303b80b941c04000c0c00c0b24010010059882c2000746862000c200550f00c03030180108024002051100000084800a49040c172501e00405449040508001000c02e07003c0032062120903034241030205181e40515404840e116000302c1c01030404001d503014003249103011181c840c1285a28080d581c0104503061010500c0445030031441d04000c44000c161068400c040d40e00896002e080c000b85030342440c04110140445c3c2c00154507456090200c0213401843e805041d00810394074009030f107200030b840075030001058160003410040d84030848011070141d21582 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 672221052 1250 672219802 672219809
    0x121107150c080f06120613111009030f150e0703020915030a060509031207051c0b0d0b15060f0d0507091a070218090f071415090310061707120c 63
    0x106901d02d98540b00001c0400c00d40e892011240d101d414100880001428903070f1f450707107011f141d030740244070130210400813040a400400000280c048408000154036002d602e181d05118000b070b102c40c3d40131610948112504139a040400781d000020030001d504117140150740203648440300d40540080c82c408203559040c44100108605d948000090071244144203171501288121f600b0038050420749030060180d003110320034005581c40d10308a04c1c010300c0f142c0300e2181e1340d24000d002550102000e13161100c3c6800c008082c0d025512801c0a01c0072160364a8005201580009804640ba00360051201c1c003100d100410705428800c0e80d44045c440000c500da075080c040c1c516018031656840d090302c0481e1032440d800b80083c1e10300180605029043c0008070306410090148422181c185560340443c002c0708001c04023842d0006000e1903a114005442c0b401004484d40150440f444021800c03500000c07282c40741d00c003c000c042e4031b0241506c001401d102050042c0502e0892104403070301501c8100360a0062710 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 672222302 1250 672221052 672221071
    0x51f1b2f03070b07050705010b01021908031b040f230303041502100c0e100c0804141f0305010e1f0603020a021014090f1f020a121107150c08 62
    0x60111400d40030012030714101c1d4416031100359400c0002d00584550400e03038045960b54200b007400070041d48001071100c280800c070102640e81d00c0194490010580c0b002d49560004007014000c3d40c008005800100000d003100c0141e50302061030722060442402a1007410101020381c100708407200d580010030f6805640104003104081082c20800f603107808048c001500003541400300b04100c680d04000710890203582036070300107903000780004d084442c01c1a00c40000c00703044048c8414040e030040880c0d0b4040b40b00003d00000344000c03c0000400c10706051040490010b40c80714014800a07200e480c480d0341103120125007020708000381180400c40140c6000e4003040682c04610344c16468420031a102004d2480001001011b044105a1030032920031a6410080d2281d0411540b03103000020303842c200700346008116028107808640c072101a500204001040244641001c40702c0b1040d03114246603c7c4440c0650303036560446141064000c0132407a6002c00322440e02c6c200ca00c0094014126175840a110f2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 672223552 1250 672222302 672222377
    0x200a180f06052b0b15090c03070801090b12010905030d060b0705070603020d02040e0f0603010c0e010804080a03110f03100909030f1808011e0509060903040909051f1b 73
    0x400e280340d410241c8a40141ca20481c41c0180321205017250036800456038243d401d02c00d01d40e100182c030011031200703860082c000b611000c01008034281d60752120034807500003031400b00c0d80e14030b0318409401c0d642104820303243d41d007000420204000c02480340c1c800500150f40101e08048061b180c15841c0d40152188a00b03054000030000c0700326540340c0c1140e01800d84020a0340700b90030850220342c103000088940c0f42c06503180100402c0c010f4080c0c4201c5a10300016507500c204e9995580e1034002c140c22640c034003010305444411525043e0b08101c050010b01100300300710b507200d00e0900b0b1601084000c69000d00403440c54642c40f43d0220750301489402200b105c909005c0e500b903045200c034111180c1c060b40210059481c1c0804070200304041c0c401d10302140c02085040c0025112014450303140e05040d40c0d01200750b0b108000420911002e500030b0505035001e40103403040c054014000e1420702000c0703c20310704190303991104880600e800112002220758980b80140500310224200601840010300d0031400a400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 672224802 1250 672223552 672223609
    0x9091503120507050d0305220f02100c1209060f0305090c1509130b0d0b09010608060c03010314011a13060f030f12030e0604200a180f0605 61
    0x410100011035014a144038855007526004005400440d000c1300e0381c2c01100b07003a0640340c0c401c1c0503150280d01c119003004001c84280c03810900c1814200e00843d4445840348902000da80c5403c00c07607501c0f80700d0342c44071001081103203040c201c40b543c1d80c440c10052010542041c41003550042410302650218100059551540c02105141c484043d1000b0303888141015000703e20700240b005005012010354500520800906500c2c05540c108500e241c2c00480001300c0601040188002d640c0104400c400060810b072a4208036040c02c008503100d020050001004204202d2002d202e0a400c00d16900200300d02c89428101ea0a0b0402e00102180320310101106a180c06420f58000385c010710003101e84050407642d910f0f01245000c031502d01503694103204501c42410902034041e4141212010000c0c050554a659660400700508690b80710781c0740e40e04136650090b03110a14480c004e40725544035014480d00100d42c00d0300795035458503020641d03410100c04012a895207404c42c0302d940c0c000b000741c048440300f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 672226052 1250 672224802 672224831
    0x10803070b1308070f080c010b06040506031b0f040303200607080c0901091d180d090515042105060a15050904050c09010b072001170a021903140f070909 67
    0x510800035010f0320400c0e1885080006e01c00c001d010b40d280c60802480080c400e5010040c090090380304558014808200003405c50b4564006041805007001010b8103225586811000c5030300941c108a01203400798040124011600305020700c1c601d490b4006058928002d44028031301076000c0c1141400207400700746001280c2c0a16a00009851328244900c826400208074010020382034030307800e0b040c1c0c40301215140c4041010403034010210154480341901c0340b4000c24810030349130088400e04c52203c18080460114802020f00610400c01c1d400b05006c40392608040f800c1084c054189180145070200c82030501c001d00c2c40b000d003100d4049078104099919814075034100400518040d40c4000399100108040c901480540f14040c018283e07001d0b40e40c0404000c4c0003207610010a10b01158844d80e80c450090700d00b0082c40c0d03001210304070260401c41c2080c0c15001041015220101194513201c815054442030264981c1c00000c26103250403d0610380c5028040865501401d24995240d4028504050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 672227302 1250 672226052 672226057
    0x103020c0109061d0a0519060f0501090b0a08070503071e0e0c0705120f0301050d061b2006070e0910080a08030a1a0102100f0f050109020c06010803070b1308 69
    0xc8100d4002d200018603890f0000c020415951844200c200416801004280c0042d62845043d84107004101c00c01c80407035291480c48980108851460f151005208100601c2c0140e5000701003882d4046170018614040013044807a80e0842409517000702c40811042d600042c2150407034080421942d010f415540021480b102c1a070040c600c0302c42114140018002044002d04041c0d0060041e9040785200c0c40746084a880b5643d407a2010700c001b0310060043c2d1a141c001901c485101e010300049040d0902807140807440000c0c03010b008951004000d050070740241648a40c0d01c80c809000e4980d41c40c100b08043d00da0640c100b201030190a600c800140c1c92102194900702524a0f441101d008594502d00b82c01144c0c01149c140740321508200244a8000035149000145001600540901d000c01c1c52400010080c411f0001c021549580c44c0c511440480d00c1480e000c0c01ca03d40c1c01503521805040f1003803604a040c4e00400d0aa8400c01220f0701040e0503c1c07441d90403180000054030803500302c3c01c2420301030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 672228552 1250 672227302 672227317
    0x606040f09060e0705131812020f120c010605190603050c0c07080109020111060702120319090c0602010509070e010b1605010f090c080c0a090f020f04030507050f090c1206010302 78
    0x245401c050001d00f0100246800448100b11001c0308000c1c0d01c0164942030380c03441c0a9810180741c1c980c8407980003a584106007840b0310001c2c81200c02030b51300303030407070502e4034a01c003d4503e00c180380020041e2100c502801107a01410060754615441090703600c14413940c010354030076402010b55500205081e82080002c6844022000088880068803180e1030b900038000544c040740070a070545c29983d05620042079662140c4003e80281202544650445480c0c5c0e00c02812880041802c143c001482c429904c5070140f2a130003030850750750141c2428400307421a100540b40a400d980f03d40300070400700e0710050078141941c0c0b40c100541d8a44020740d0003118280b031070040043c010b509080071180b04064507400380341e810f4014003074540c2c0d190340c404245840340c0414080d00e030442c03000c0200380007d01280d0425446600c26010043c540703080c820740010141c009410071603842d005030504005500c1c03d07002900c502d405c02c0300c01d1f004500b08400302c070141d4410343c51000e0300c802c0c1000016000341e000e94107941c00c5c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 672229802 1250 672228552 672228563
    0xa05030f0c0f0f01020a030f050415090602041d0405060106140a0507050703150b131b0c050c090412020f0313030609020103090c0f06090b03460b040b10020606040f09 73
    0x89484000142c2c080e40042038101c0020f49400c00720014002c8c0c0c1d00031140541c0c0c1140c103040303180e1001b00000000d04403801081c0c4255400308000134103003038a41082c00c0030383c040c4c0044101d5410545031803801c101c41071740244100700c5407440b0102d4405281c5d080b2000b00d0a07905026a80d01c0f240e240c101e090660079800a0020b04030683c400c07202c0da07403642040c1c803980d10849000400c0400005003004440311105554004d550040c0c9107040a0300441d030f098001f070300550888124850703010000750341d4038080b101103903200e00489841c030b03820f901000102019001007026600341014141e400a0944040c400078168648400c2c2d01415039010303a00555203280c02c02801242e454a8540072051441141b0501c00018004000040c1e1406c080b0300b501d00840d01407c81080c000188074203a60074001c40444000d418404050906084641c03ca408039210750400000c1000c010100802c011a1120b80740c541c0200040c000840c07041c2d038045401680160b0071240000e50b1034125208200501031014010304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 672231052 1250 672229802 672229813
    0x70611030c071505090c01030216020607060c0f0e060a0c0629030c0f09060906011202070308100e06130c020a02030114041e0b0a1107060906050105010806030a05030f0c0f 75
    0x4250400350041002c0c0f40590714a1006410310080c007021101c040364650003a4001c0c40e64084103602c00c1d0003d001200c4641c0c802440a07a032600000c066900c418803c461180d80c5108a0904076004280d00074500c1c02401c01e43d0031540b00c03001107030f498030561101204101c1d040b180b440401c107055000100d100145004400740c180340644c4208503400d1480070920078424000300d810035250003e000321801d4070141c0390140c9902c807402071028888014003802e040c0031480d10450709544c1e2a201400c1100d000790f8a4400c0d504044c07401c224007074010b41004400030703211000c000007505d40c020030069011102c640020a000310800882c10802c0c0f1007402585942803004034200d40d0043c2c04000c0c0100c3c01011010882c1c8100c00b1045440c0745000001400040e0010014221040039840301c81c002080701306003483c04205540e03010481d41100800c580142e0703218014000b07541e0101c00503501560503070082c4a400c03400c0d2180c0342c7e01d0003112404050724200280301c2850b108184007186095410707408a85 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 672232302 1250 672231052 672231061
    0x20c0a0c06140418020a020c1528320c010e010605060a090b0702030c1c05010c0302030712110904020703080f0603070e060f010903140703030e190b07061103 69
    0x120211038440d2900041d10396101c0041e25070350b00221411180f12140384581c20300300100d144065040010405c0560040246980c80c5031036200c10080c8520701c00300c030180e4803e11401050020130007244190034441250840f5040a03800c034103522030640d9072044442922915600d50301c80d40c0c04030000c10548031808521111107000c15000074150400140c0244100c64a4406101d058022640c071100028511002081101044001441090f00160903143d4895022010515940c840107035400180c240c0340560040c403400b031280075800380d2245410340c690b0400000042070022501c0c0300c0c594003661f0301044039a0b80184030445a10b0032002c2d02c159151b98003414007a00c18402100c410340d402c84003400141c1145008500c80d020740d46052035840309602c5000601030741d000d0540941e414840082404404034055030305d101c0448060800074034900e070445c80c0090088001e40c642c03d02809099018800c0304446502400076240c08002c1c0a03111b0030142040c03800381c020204000b113211310000030300c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 672233552 1250 672232302 672232313
    0x2060313242705071a0c1218010f0801051002011d0c1207050a0b09240a180f0b030405030f1810020607080f130510240b070b0a020c0a 59
    0x80707803000084011203546582c0407202d510340b5109800000c015410400c810300c0f0480d24015440001c141c0310444038108000000c0b114030f000f550410303810801402103015000c44ca103020504282090a2800f0a03c414000d0009400080c040c041d05100c7e560315004120214401d60081c40701541040002c90311040c2c84450755261102100120b000c6d81402c0c004940c1c486c0300003440012180003501e012003441c46d01c407040303840307401401c60716500000900344a15000c0f001c110301048024240c0d801350717407802072075405007448a8280b141070071890201c9040003117808105640c0103c5105400543c0e50b0359541c60901d045120380041c1850742900415840c840100c00c0c1c0000408000c282c4000107082c402c1c40090740d6680c4100c516900140c00e10f400141c0304202051916080310451141e40074280c4c0030794805090920501200c1d0180350b80340e00c9001003c16441d101c03030b810044880e00c0c03211a404d20000c41c5081c421040c028001c01c4107a00880c41811042d0304651020a132074007030350406805441d12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 672234802 1250 672233552 672233561
    0x71b1a060a090e06071b151a27040f080a080a05010501030c0c0209060a0f0b03060406210f03020f010f1b030204030201021203040804090923030a1b150608030c10090206031324 77
    0x180322404002c812a10542840d94409a8621084610030120040c103064201412700c0248103c0c1c04481071004100041d075200e024003240c0f0521386900400b49440070070383d001c503501640320a0426003044400300100e03030454000306849c0d4050310b20040c15902c22010400500b181d5206c48464821004002408044c6070060f5002d540100c030f00740811075503400f2404103038048000100d4110f88405800000808201e540408148a030040e0355450824917121400c48086c52045815141c490441401c480080610703412601e0301400c04504103402c580000390380d0402c840000d0118031000022900344503202c003d81300100034010051081015502d48480c9187d140801c107007a14080302c1c2807034224030020007980c840e021507640e08241c8050003148a448078880c410306031002d9044408103005108035019010103040508010740c2c1d80d10003138101615144100c150350744c034603251006840060b60380d1003c40e6041215040c2c10200003540e41442c011010315901c00d81000c3d4400b10350800c1184c0703940c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 672236052 1250 672234802 672234821
    0x30c040f09050106050912120c0a11100804230703030504030519080a1d0409060b0112050705090103020a170106021e07050306071b1a060a090e06071b15 67
    0x510351019074891128041d50420302400c800f00c1c10a011009440c01d06488840f5084841400c0320544460207040449681c81450b060070190480c00b440c10a00500848405629000761003071403240c5600304000b05a60300c041c10007401038201800c4194940d4007400800d85046c0c8180a680c0c4842c0d607894060110341c40b502c4119918000d4021203c444000c803d007002011f504000658a00340440404907061100c0003444a41d000702244540c450342c0300e620407080214814036001a01e00c60003030001d4160030040142840320b6051070f00700411207500c030003510344516081c200940c81d50410704040e22001c041c1c010464a4191640c000244541e001804120041180c1d101078040080c04040503114111405620f41541c08000032412062140c00005000b00300000701d0703c001c1820b551f07050602c100c90f000015130b2499401c1030100501e00f030341f800c0009099000007000b0700c131800400252208030003842c9038103120084141202c0300341400da5243d40160310500c62039103101e640070400001c00e00c050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 672237302 1250 672236052 672236069
    0x50304030903080c030a121a220e061803030709090c050d020c15011d0112061b0302090f010314070c23031e0901050f070611030f0a050702011a09090c06030c04 70
    0x1108070f40241d1480c400e019420055220081d002e2501c4d000344081c80e4078030074488000342c0e20b862084404546510603c095101e550028000c123060cc6100c01c0320403c9042c0565645e42c01c1042800f1b51290000c14150468401d0300002c1200c501d011029940350061041c4041d01c1400000c1003041d01c0e0740412103c180000c46842c0700501e03626072031941034411608885204d10440d441c018424520f0280645840512030140030170041d115656402071160f82e900c0b0300022940200b850b030081c0c81c00d0b2240b841300c0c00080c82d080000340e40054070040901d40c080c0c6038000340301030b0008140c01d002c0c1c04801d0100030f40c0245a10306007a205610141e903654040700f850391042440407001c9890380f11140c21036007a140140c0d10282807020650214016a008850840313040340e4660001082074280f4000d5480707045410b04888892400a030710320240d0380018403850440e40352404010701c89034500300400000307106548090603503544003000c41c5489140180d0036845a000300c1040f044444841c001c0c000c0e6034181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 672238552 1250 672237302 672237317
    0x708010b0d0b060d05250e180901020717120619030308040f0b101809080f131206020909102303070f031110020d020715050d0c0908010e070312050304030903080c030a 73
    0x19902143c8103007d000c45513500200c2650410115882c45030365640008100b03000500d411902c2e5285c040746468000114007012000c00c40795400f072800c4542a90024089e07410b00e0100c03144140540d442c2d8910300006044c400d4a8000c035051140000d2402a01d507401040f401043c04c03c1c1c11454145c010f83c3c480c020505a113465a4980309186010700c00e0343c02c0d40112a075080600c0c04064400e69004a900f02580303142410002500c0c140b542900a00a80030b00c2005980c0d0306550103001201c10010494080268502020030014021140d0800580b10b103619559154000d82d00103824250140c1c095035404400800c0032040c8403005000c0e401e00c1d1011200c00083d0704800c101a80c0307524040c0010b2001d17822048080124460710700030070503410398a1074158176001d006003a0074220703500e401041d0f0001c0d4440205018120003440384402e24180e0100a1101c42d1840c1c0d115246101c00c0c40d20303030007040404808141018090b0300c5200145601076010b50b220429944910f03980c0d0003103214500090041d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 672239802 1250 672238552 672238621
    0xe21010b1207170a0b0408030a0e16090b060408010509070501030c0914060d1d0a06060503120906091504030b270312040c080d03020409050708010b0d0b060d05 70
    0x81c240800c40c41c045009856a540741141424440c1d0001c00300f0361076800f84001d49000160807412040c82140720707901454a9003444c20011044541a440007015941b10303008106042d00c41d0031950045905140c008181365940d4408140039000e9035120b02d506609200038080000030106401c0203460080c1e0341000a201c144134102c0ba0800c5511501c8802c7c298050800f0782030030584c00074404070841130404201d00a00c4110310589111a1031102d0540e001f4080d0301d804c2100f075009640c020a8210028607500c40f00c041a0030b01c901c184402d8500c11035000505d00703116100d16000702c0405001c000080e85440d071300c0c240058690000c07941d0280408540c021108229035442c0030b900d080748804001c0d82040c0f44a001c2000760030001d4130907a03441140c03410020350b0300000c011074940b40034250340141e200c0340707071038030500a6800240142c014040c0b0280140300e014032785402c0e20107070700b446403010035045298000f06503548110200c0c032524a080400f08800144000100300002d0b0207102d2400f0700000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 672241052 1250 672239802 672239809
    0x2703120b0402091012110301060216060503150402070204090204090c170109080301030204091b120c0902030c191407140613081b010615110d111c0e21010b 68
    0x2600808551100c0c80f03a01d103941c40c0b4851184021400785600001034003d9078501002e06c00e801c01d0340b002c80168490038039100c940b02044914401490913003483c6056007007003410000c0c11104075010b01c0c010741c0e0100341c0380159600c0740c0081e0292600a041002420f0392410300212078003060160100c01e00003200002c0c01544144503038003d103500424210b003107134219800c11029201404003581d40d01d00b0900b03403003162111010104010400c80803070707200b851040e107403440c4003a140b540841da10b54814401c103e1281c03920700449295030207110564810703c091400030380d25908400401007401102103404400c10140e400aa000c40c5078940031101c007036950058401c0840c082810013000f01034280022800300b0400311007402d80c00942000419216241c0070601e54048411008200040c0c4500b4420b0b000d28061028401030226072401c40005411207441c9a036405500c0980a181603011401113034852050010011511004040d80e20641104d885601c0b42c0180300303042c2c11a540f0f4403420040d03070b28 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 672242302 1250 672241052 672241057
    0x1202010e040905061f03020a0e06062b0b0441010f14120c04270b04020a1208070b1005041d010c09030b01050f01020c12060703110a02102703120b0402 66
    0x80e401410786101500b27081c0e04020245004d090540c2108040c0495a0f08503103011400c5d01c030030042120404400c010500f031005558a01d07141c28051440c1c10001c0c0714010b030b80282400c803290601d20031902038501d0802e009401030a84500c1200602c80e00c000310303a80281078079040856a080392140c402c40150742c200840168060040d000d50340c0480140b40c19070500307030000440442c090303640e403000e03910301c41c0c00d09002d8032006021600b080140b4204011850100c40e030101801d8000d01910710b020256884049501c02c400700a42042d08040029061040038400500a000d000c0d00134083c01a1842c840c0d1811194101015055420701401940360b81c031420b400d10807070350003c40d0b038640e50b4038200520501303003110014207045004690038413845494240c180c00302c0c015044020441c900e80107200400b03c0d00c04a11411980c0401c00040d5052f960005014400c0380c40340710000382500424005401c0569185100007190b0441d0600b0702c14550401d0050002040c440024030800c1c81050405c012071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 672243552 1250 672242302 672242309
    0xb060907050d0b01210617010c0807050d09020406180608031c020702030c0904080316021f0f20070501060b040f06080a090602130311191202010e040905061f 69
    0x510148001c410b1071045070805518001c1c1810700c618040d0244050002200501c440e443c0d40c2c940310351040060110104840c02810f800d20001c1058071081e00000300b0400d00501401d0800c880443c2120010401d07a02201c1c034613600400c100a030703541d80c4000030b21000080c111100081d00c1c000c4002100900031007150702004440405036009423540c48444c00a4100200980c0c00d4822003d1070f11068907251100c0340200c3c00742c680581c40e440e0501c4445241041074043c0011900060501d21005030740103c408009a40700902003001040c04803c00b00a10088813110751a06d030030454055403460080090000d14080c00007401100e84542c8080320510540c450311045a10950341003003201d10400d00d0320341007402c401c400700d00d14010f038a0f0032003660040f0300c9100380d80301401c40070010083c86003044250b118046c1c40030444201c204000f000072440a100740100565402c0c4500c045a2245800c0840388100810402c8641c026040150341d9940884850400700d2000e1262100c511024000c40d049 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 672244802 1250 672243552 672243557
    0xc0f120501270e0303130c0605070302030313080904090803060103060e0f07050309070b0f0a1205060d060b0102070e090607020d080118150504090b090c011b020609031c0c0b060907 79
    0x2021402c09004195404120041d45050790742000161050381800290b004440c243c4401483c90030318180001780341c110b41e200707805000040140c0c10000340c000c400c4d00e13440b4004c95980e0104200c1402d00210900c40c504e400355015140529140c1080381040256001c0c030020399003002030a032101c0c142c0c1190301e400c1c0c0c0c00e010340381d42400020740031600c20402190700c06610f005035120580e42d0b000d160a9600010103045903604046182c60b14280d200281440c400314025042c041801c3c0040898071803298401d016011a1311520784002690080102c90010a2070080340d250078a484102544c0b0b400c400e5440308010b014851030440882c2c8035a40f080c1c141c6091002604440c91005c0000000700b081c0e492009404000060014641c0e85501c5015600741c0074055142040c0f500010150808023a4501b640c1030201c0c0144039040090003800400c51903606440d01541c0b0000c090010703161000c1845628207a05604070504007890b48004030400c030500c01e0341b41c2203032600c420040015900d0216003c0c1e00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 672246052 1250 672244802 672244829
    0x504030909020a1e0e03070605090405100e310804080f0a0210082205030c1513170708041d01141806010e090108030a12090c05060318010c0f120501 65
    0x13002e403c109400f241003054180202207030703903410209080a00a505c010082503001c82d0007076075820540912070b8080396801c1a210703002d0500140c0d00c40e0400182c42d0403e03040c101ca61140320b80c4c0c2c4140b20a01d015403d1040b0f138000307844514120b1215401070007050014000d82105070300c800c41c0042e001012542c000c1040000b1200200c045402900040511011a040141c00d540d104d0040c1404001540580040d5a031605076005c02803800c00d90412502c2c644000b182000048003a4400072000d80c5c0e03114120350300c00c0c90845d907800340c203010b1818080c00c1c1c0c9900050000c0c1c41903100a50400105000d960300c0a01d03030380c44d4206980455409003075608100c480070070100016060b5541980000d0504000c074402c41c50388089840c0e02c1c0c00360844c249a13030000420b42c1c0c00799000340e00030400060401081c01450110360768036810391228070499003e024040089403881106030b50442c10304c01140000c01407000d4194000780b80c0c0502c051300c44003088540d0707091105d03a0800e0040506840c510344400342c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 672247302 1250 672246052 672246077
    0x4050a02060d18030324080d0309110901060c0c0806100504090f200f09041703180f061b03040b0402130b030109110102122b18060504030909020a 64
    0x200642c4203030b120b9064640c0c2d84060801003401c000c200030f81d060080d6000294445025000380c2641c4100645620020701180d00b0400d01c0d10000e0641e49448a82c40c011a5034409850000c030801413000d42e00d5400f5200d103001240b600d600035038100c1c01d01e000f0169410410f0b510b02996864210640b8a03000800c9480300503c000d00b441c0d005414414410002c200264001da15200b00e4015140c1001d405406e01c00303041c0c400742c60030319804081c591007118000287d0905607914180405200089120f140d404400100035505d2454100c6000d10020190740c6a0000540e14940f50642150f03002164410307070b50f02c40c070600c41ca041500d125990206130300f516502d0303030380800c4802003507088a00011901c800c0d004402e603d0030700849400e14401d03044646040d080000190506154000d103400b00501071105c918450550114908c609181e000005d0b83d040300420329001074800402d0300c0345550310600c10441004a2540200e2180d4000e640d0506170f95152800070341a880361a02050008041d1298071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 672248552 1250 672247302 672247309
    0x120c0a02240703170a0605011e11030307031506030e0d0c1104020f03040c09090f0b0403050405040204081c05041a0d090605100315090c0e09070801051501120504050a02 74
    0x1901468241c81c80e00000c011240d0400c0d1a680310342422800144820101921000b400b0300c99904440d0f21078042c49684e040c43d000030f00044400700560024610310041d49400c501844220042d002030001303481d540d241455014025007086c1c081c0380e210f803403d414006001d9100b0300ca8030380c40e440f144001d07201908804a080382c02040303e0409550321140740c0d1080d18203039218070041102c2d0b00e2022005c3d0b12031400e070800d61384025036640076010f103a040c03190600001d00800e010210890f030001490f0b6031503e4500b0110b91602898111035000b5100040101c1c5080d000110210ba0758424404e000c81d031040c1e46011201c42c00745c0d01ca0420003600351000c41e61400c4003031025103581240c1900c00100e00c54251100c806031002550404c07150050348500f40306010081d00c0520240620000502080444d540e4803200071005215800d4046100d902003480141c050000e00e00030304800d4001d100900781790f0b07009012000300c070050601041da00c1c09000640101400391601c00c907004401381c903021030943c090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 672249802 1250 672248552 672248569
    0xf07110a05062d130801050a0c090317040806040308160905090c0c0c0a030c03020910080705091807080d020c1f050c07030602040e060f09060906040b13050c090102120c0a02 76
    0x2102c010800042c45143e01500b024050b181d01040440c40810441c94000d900d821100007a14806041303080150081e001e6401c002120f0446c0e40c030140d00034007003494411030b48040c06560000039207030140f40d0501040c19030041d04203015406492407840c410080300c2042c0c032504594800c05801950000004940c86400f4003c3c2c04144400429100d03240303003140000e108500f15030421103021194072014029414010700c26548078103280303c0308440740d080c40001e44e078440c200e1180703600c40c40030b0303030002090303c440319001c0800c070111700c070481d01160707141e0f0040d9481c4e004281c0f4280040c801e4031050031042c030b803000b50844000502c0024840740c108100741110103500155030b0a50a10031810004000390b464801003000b00704d502900d140c1428070b03404104400000c41d450b241318055400500802e5503c1e04260764202c1c000720350003d002c5480f8404103298140511003134030b400c0c3c80c103070400a0340440d1400400c41c94000364250341400c003000c0910401806104a5140390358008c140340001800c00c0d901d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 672251052 1250 672249802 672249847
    0x9091703250c0807080703020c0109140907090b07050a0201021b0618060408061501091a0d050619060306080610061403060303190e0102010e031c1e020f07110a0506 72
    0x106030300801c0042d00c0383c038215804888201c508110026000c0c081c95814400116104000d03c2c04081031894410000546190002068070a074118000318816a0152140e03100600c001c0110035190001805c0c031075142c1803e4881a400750103540c03003d450310303501f0014814800c8001030105007003203042d0904c03141e083e01c5040c115820010412011481c0502003104500ca0f031380c140042031202c1105c5000601d480800c3d801085c0b070025002246041c00c070207105840c031300885414009010359a0800007124001c403904d041c1c03111030f8801004580d03c5e50640058080c3d50503131044400c1d98980e490f40e100c136090f2500c280c0c070014043d400169030700322400004503003005009044038104900b240c40c1810385159840d4550200781605841005540c082c0200f021241ca88409181400001a1902ca9840e104031141960729500d601803400c0f0149005140c00c134500001007152211040c3c8d8984983d90f00441d01900c0c5d00d9582542040740f40303000c540504c01d80302d01511903401c00760301c54412424002c01ea00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 672252302 1250 672251052 672251057
    0x1c020d0902121c0504031a100312020a03170108150a0f0c2615060d14070c022d090604090609151a0f0f03070b040909170325 55
    0x9010400340c1d0b103070540e00d00890000400b81000b0712650020b038000b03100d000c1c2041c081c80b406000800100c4d81d000c065144040002a44a40903a9035050812010030150030050801140018103208c80d0760008003107020f04e00c25100c481d450030f05102d868017081d40902c0b50200340d61180f90030148034031500300741c25082440c10b200450410184840780c0c06a404241c482c40c00201d90b8250540d1401d520440010100c18002c207807507960501d0003845000c201c000c01202d024120004410031a05003540c00040b03807c203034401d104100c0c2400a030050891040c02c600303034030582e500001e1404184004170f1510100e0000040d00481d60202270034012010001840d83e64010781d0381d50b96001180c01401402510b40c0b02d550007045400707800f01451304681d5051610aa040301c014103030001900c41c080d030031f0350703181d42107820340c41820356100001c0c50b0880e503402084001501043c000313125442500b044080c240700340407452031a00d00140460b102c0c0000c65802041d904c100f44a408051819080b4000c2c1382c2491 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 672253552 1250 672252302 672252311
    0xd0204020f0d05090d12020a0905040510090f02040510110312130609151512020d0f08040b07050c040207080a0305060604151d0901050d15020910020c151c020d 70
    0x10070003011501c1c1101c101c0e2090f00b02c5c150b002e882a9011291000d0700402401c11801c04c031081c030005203100e03150b00440c2c1c01240e98070080b070b5461400000e800d004000840341800241c40300d9100d88065002071203002d001d956180c06d08941076006121855080c41c41c50000e500b066050082c803280d96a0182c481407a4490744e001500c00318100e4005c0540c040d01840703c000e80380d8824000c03002110005c581d0100c0007040b09209000c03800710000c2c4a0812601242c030414100654180811b40c0c0c80c030100700400d41d800000e4001040d031190000780007030300d00400580c0e0f120100103080c03109900c203003070300142244400c1040740c0580d80286e0102d078203c1c102800640c20151604503100c20b07224403942405c04501c00e04100410300303c400c46000040d90381928807043c15403401c004541105411807004012420301400f12101e203140340d0550320181c5000b0100c40100020840294680841c59031603405500c007800e204045070407900840f41c1189000e4046401c102e03c520b080c1d002174010f403d000004036100c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672254802 1250 672253552 672253567
    0x27060614100509012609150108070e0a0e1e060702031305130905030c15090c100521010f150e060a0f020703080304080405130911040b0301142706060d0204020f 70
    0x1002e41611740110010035608107800c0c031080d0b80d45005081e48078030000c140d001006020080003c6101400c54401e21805210f03512410f142c81c0103410192281c0200d80b04490401e82101c844103140021000e242c400d40e051038880741000c903140d219049a0000440c42c00c9070030002c83c10b008a84550407441e5030400100d200c0d16503034180c155801800f5064403a4454001d50001d050120803023900101040010688102100c0219803c228000f030514103100001c51f03c9d038098850b216840166004c0454003041541c0c50703010005010070305009e92507680e5080801d62040074004c0d00d41400b00341c8014030140c200b01b582c890880e4002a0b06201400f140030307081001001554800103140254843c01034035845505010034401c030121a01c1040c2c2d41142002c0c81c0328046460108901c00d800c0301030f10041600321001001c0b0b03014000040c451244005124104201d18bd40e0348508988054220124041c404144141a990780303010380f6215440301d1400186401480d1590091811111612901d41001c84 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 672256052 1250 672254802 672254837
    0x6131e050f06010816050f060a180b03010905070c0c0e09120d020904110703090311040b1c02040b040608031b39092401032706061410050901 62
    0x1a8200da07a1800e9218200500a005081c803641c2d01019460061300381c02c900d880d002908128810f0b04850152100044d600c05903489084129800c180400c02480b5965880b580907002d5403003485003200040c541004036038014820308210502e5604207005400c05414404c01d83c041c40340103810043e6610a50500d0700003501201702500e4502481c10340180c5480c10201400b060311a043c80c0e94010b60800c100b10400613401440d40e40c1902c1d0024401c000c034003601c20101e03004180e5010342d180c2c0b0204d8440a420200d42141d290001188240c0e41401100300004c144002d4810600072103100b9001072091140d074910b40c01d815448220000110703502d031000240941c0d1b030411100442107195640c03c41c800007061852410083c0e40c02d0a507101e070f0070380c60f041c2400e20f034032074224220b0944908840070001040e84a0381040b003911501001c841a5880d520003851404003881c40f04130303081d9003032980000b1200102e0395600c90381040640420558101c80b00100c0d007030341c085640715050102980040b100c408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 672257302 1250 672256052 672256063
    0xa0605180c0d1d06011d01060507030e0a090207021912150906060b070b010f0b0f07050a06180204053124020715090c09021318090b0906131e05 63
    0x30290039400741210b440346012404c00d20160003141d0015442e20028141c1c01d241c038000740c110341c074525006407203a130719280498401e100042c1c09170780400402008145240282c1c002e1248620840d001c407005480c1c480b000050f07072074621070081c1102159041c0b0021940048021514150441c400603415103035644090032585903400c40b800c1c0e0000426003604000360843c03070714090715552a4a40c50140f401c030802030640309807010b40303a504901240c200100031041100d1010b1aa1040d03081c860200d09495200c050524400300307922460400011035002c0980e4904d84001500b005824014030340c2800d004089038016032030031a0600803010090468508c0c80491050f40e110005026940d2542ea007028140c07109aa1031a1424a141c225004002200b0803c800b007241c1c6500400358032242400c20550010100b0350240f04440700002d03a101d88010705511540d6003610602c044003441c3c603101c1e81a87e03204000c840082140c1032041000020580d0315072807442c6600010400340c0c00303092658415082a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 672258552 1250 672257302 672257321
    0x105070615060813051c0c1203201314180c0a0801050f130c020c0301050103050f12040612020729091902090f0a0209030a0c030203060a0605180c0d 65
    0x1d29040e18240805580003414507042104100c90481d41c40f059180e443c1c581d0842c0d540502840d4003004001c0155000703645d2a40c41d143c11080242065246002c0038020307010307124084002102212422145110300c0041d0741200758040700f102001d5060150b80d88090b071001c065583e001040c9440c481110840d10105446445c50320724068a81503000c0c40900070300d42c10703003101d48a096160440b05903522900600351420f00100400b01e40c1c45c8000c0f070143c4c10500140c41694055003440c00101c1442400595844090000001c441d845001c01980e40308a025a02940000449820f64003605204640140c1030305130040005402c003164450118083c43c00d5820400303d10002d01c400c10052081c00d208200e19411038488540c020059680000e003401d0300100498032010110021800c1c1085039030540d50402c3c4017070100d60300c0c0415410085810201071004038464400c1000181c4524010301900d1b085070f0010740300e8540d02001c0c8610f444081c3c1d0040845810344024407403000380205500030441c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 672259802 1250 672258552 672258581
    0xe1002120d0603150c050910030605031e06010605040602030d0c0e040f0b090f090d180b040303170601020c1503070e1509041b1704030e0637120b01050706 68
    0x982c1e25500d031100c5100181065910075900e464003044c400c64011301152121201211f11103000e40c81c40005400603c05a0842601071140240d8880f05006c8419400b40c103000034411100b06a0f40c500d01108c49108501410303006800c01e11001c13501d462607800035420401503041540e004034000380494100c0300b0603010300c1c00d4991501410b1480d81070541c0115008514600c0c1a0700070302d00700e0f0a0070340c2c81502080807004c0100d1248402001ca241e14240300c0075021001000e035655959040040400280040d408000c44c1004003089140d8000103000e41c20b00d601502211500c10045d54064aa410041051040c400e401c3c0d80e1180d41e0307507000185401410010215074442030301c2d43c140f00c01c90301d0300400c484a0f000540d442407001034002c1c202d1590f01c010303c210300b12241d641d458102c0d4020141240b854000e000814441755079030700499141c164140149801800110b0402a141400d151160700000f080d4200800e200c105070755003041c8400d08060500300c0c523040460703480b0011500c07985000b98a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 672261052 1250 672259802 672259811
    0x30a1b0f060c120b01020c011b050c03010c0f02070f03050717010f0f0c020709021c0b060c0318010f020d200c0312090429010e04090b0f060910060e1002120d 69
    0x10f02012074818101c0c0c0b040c0a1006204152045001810002e00c042d0f407040310000030030001041102c00c00810b07042c140c0250080c0b00310400d603078002d0710787c591a4040c4c5015008041c00440c0c1820a00c581a00b1a40c0010080108600d82028480354403118000d41c003095485032a0449402011b0041008500324082d0000e0440703800b46000342005020341041004134010800070040091800c0e0400d540c500d2040e00107060305143c000141c0d903224050110605000101e03551900c8c0d400070740e044055403000e0300c8110201207140e00c100c0c2c5865511905101049820706050698801466451207401c00002210366000c0e1510020345030035414101e4111032240040c50022a040c540560442c200389607581094042c0340c05099051044108c4046040100030128800e070381c0e517a40c0000f81599041a903503005420f11b450202c111311b03811680d05004980040202c3c1220750301031030a0b0121200c5a50b000c507003000d41c3c000c00860020b9481c4240862003600c060415140008005100c01c0c0d101d20000034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 672262302 1250 672261052 672261077
    0xc0e0423060115110c06090a0e040b010510110a0f030e03070e0901060909050304182904050127091407060207060908031e0a2a02030c03030a1b0f060c 66
    0x4030101c600c0c040250130880e5481e2000702c00035000900080e0654115085900c0e0940765001c030754440513075403010b840020f1410600050120104070941038407021b54880343d00454114080d900c0c0030402c3c8140c00b00791720805028011400781c00301c050140d8442c0c9800b008201c82113000a20b0843c141d004040d031000a134052002d4801c1c2442480d0061010312018890504962201da840e40298400d1060640e000c100c00c4051460302d41c009860104010030341e440100203000089104083c0d2291103004500e41000032646403107003c01d410050820074100000b005140c942c01e0050503c0c400112080481c80c0c28944520f41e052182070081d00c0154014071405140081c010b04c00880c541c00742030150010021102103003008054150341003800c40311030f5650030680b54101c0303119548408401c40f070b801e8120103608202807502980309003802101114415034800c801c04d6224410b80d08807601182e85005000700c0901078110007003105029030400c0030f0221043c0c80f8407055a880c07218071000204100d0300d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 672263552 1250 672262302 672262319
    0xd050109080301061d03010c0f271401120b090610020a0203011d07150804112103031b04081e1002030403020114010b0705071a04090908040f0e040c0e04230601 70
    0x85c18403001100280302c4008407640140c90841102d25400030040000102c0c040c5980c03445000510307a490910690705030395078403038610031287c440c00503500007031b080064005a03060a00400d01e6050b4001e0115405440fa03c00300050170074208001070944c01180707011009641c5c01c0c07040d0104544028059007800b00002d0440c2d007840d51030740000400c81052490710404035071080c070b130540c41980001101c0f00240c5010018840001c0040c10306e0302c11720700b00c0d4407031030b00c1360301202a50003004040c100b900014001460b0309240d00817401101c070947c3c003015052007080c0b0740020101904100009a800081e00311201e81c00b0b980c0115001e8000d42c2d1100c5003036000450a100310760060501d10866030422559649554071083c0070b115003109403040c40b082c001006281d10803240185166002001082118584002c0c0384c0c015100d40280d08041040001f0320100350050103226552100324401c4182c2081c000f400c0b500320142c02580d1600c0100055690764540d2090800340c6007152004006542c50038208 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 672264802 1250 672263552 672263597
    0x5010312080c09060d1803170709080c04090206130b03070906210504031103040f05040b15030f0c040510081906060e0904080d05070503041101020d05090d05010908030106 75
    0x20380082014510400c000100200299455040100c2d40307950b8900320081c0e80c001501034101c00080c01001901528101074200c4806120f6550b0740c80c000d24580d039000300c1510b2002161180185981004100500c2440c4c0b5078803441d45180300504650500c0e9003195010719201c80d6070403149410600000303101320990403c07144401071106180445800ca00e108508a0001a0440302e042d490380310004602018080c0005020058400c0c04a076140c0399504c1d4042292a020710525001354036000c50700c200c40c1001038144001854035051030f4907544656222503940c103001009009580003d0001182954400c0c071162889241307681c0780103c03410610f00f612505407640e075210000c149000020000743c0d4001113903030229a0115503079625507485040605042c41044400740015141c00c0403c02450f402c40b010b9400707103008500f0121400108801aa95004283c4460307003c110244074220181c5004d0822007241441035001203800c03456580c4e059032030f41003a000790001c140842d99006032980203810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 672266052 1250 672264802 672264833
    0x11d180706051e070201091203020703080c0c0103140403080c0c16032001110c040b010c15090b1e060d0204241703040e0609060319030c060e031903180c09050103 71
    0x300c0e85001c081781d0001c0c102d080329114500e4002c2265041c00c0c10f15000b446614001c45d040350003203590b0020040d5854403090f00401050110303107030030b00040c0c0020980400070720035076258850b8801902c45005006007500107003031030290b622500020000501c0c01a107c107000b14812a00703000455411804650300320041003415040055003503070b910750a8400111442856000d0fa00041e410b46444012603c0c104058406005100c100c0c1031145003c842e5131180d800540202100700316925000701c00910480d5201403403402c00e0061000c2101450440000c0458500c010400107110389000a2003000860350f11100c2901e81200b40304020400000766140c1003100807a02942c81c25051513003528504601a04945c06220102e000481c0380e00c04000319905800703120b2a00c5200c0042e854010044180301d42c00300c804500b0901c0815a8000010940d08204098426503010070b07808103049000300040c00da0381031256280d08414002c503041119140c00790140b52008038081d070450600919462034100b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 672267302 1250 672266052 672266107
    0x9120f0709061a13140301020904140a1d0604060b1c03020607021006050102060f0411060f04031b050d0b0603030f04080c0a0f03020102120304020316060302030702010e06011d18070605 81
    0x114403180a60b1a001044c03c0c0d6030003112100c1e214a013080441d0081c0103a0080320707002460709401680c19441403211621611100350107200014140c0c400914880340314002c50190f500c2140410000769007500252150078001d0556134089102c0e804920408048400a5000d81c02220a00210f0780d0f05018503000c180c1008000d0140d03900e0040001d42e2201e008003681c2003445000041000c010100d1146060510000c0c00c4948680c0d00300001c0903076920604c01100c014640314240d050300709840d004e03241100d40c000d01b81e110030001c0f0703201d40d500000001d2901d949070004102d0480506c1004020748040c2c201e0100034692042c00806018042017035800030212030034071480c00c00050b03034000b60144402c0c030404019612030f115480130a1512030040703c102c0c9080c150a202094160b4160f01a5104140301d5000380310820740120256102c110a00603d00268100c0380214008450840110740025969070440c21461001590034104907140d0010700010303000044098400030071288481d00c5903d0712 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 672268552 1250 672267302 672267307
    0xa020607031116060c0b0606220e060f06040302120a021009050108060603090c060f040503100b09180d0e0d0c0605030f0c0307390c0911030c09120f0709061a 69
    0x10502030513100482e03100821b4851054005a881c0e01d4102c1940c1e03c4807000318412482d088032442d0036803100c080b8000c100d0300d0500c940008105181540325110400e002034507003882e1600710717024410500c1c1410302e020682d100348010140161600e000303d01c18484a81c0c0d500c1c03c881d0800e40010301c100c001410461042e1001e00034007240d04004240c482c29070400702d40241d40c1d0902c58005510070b00450740401d0f41400340c1c0004440141c425017040380303a0203007101c01251030382d1101401300303030300000e00c003100200c0d80502d08018844c2e004100c07100503400020406c0d1201c140070b81d1000301d406c01d50f41004000460110034407004a0000c1135550300300c505400c265086140213a401003010001610342107550380e420705402440b903010100451002000c1551030b5181c042c90500d101c00340740ca0b100d4480900d10780185540440f01000617240102064405240b4207107084c0100309510081240d0200710b80a4407004c441000000c0107854004d02034440c020501a29211828200c2c5402e0300140b504180304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 672269802 1250 672268552 672268559
    0x15020a110c0310090212010501030c1802070b06060d0204051e150412080a0309080c0106060e0312030606130806130312091104050a110c071502070e0a0506030a020607031116 76
    0x1103200115040103501c0010b411135240000b401d00520344c0c10031402540381400101c103000c038014810040c1c90540c00d81c1d0001c0a11507202c08201d200d05d10010b030804031118041107040c50444010a05181d000801508107901c0d0800608144151486644914010441d020351414407203090a000d20408a1807401d2600d848582004261090130052800700700040c202c01041c0660311114200d500316420307030f072281c042c0e5551500030301d43d5000b00404103200342c040404514000602e0310601000d6010716003151954402d00c01150404400c80010303403245580410941800c2041034031803407030114a050b82800a0a000c0c2c0856175054074402281e003031044000100300d9444003007140001c182d40000701580d1f10481e42c0000c0420285034080100001014100210009094401c0e55000304081c510080203803000d0ba0340b10325511503a281311803680c0009042c03079441d52000d42c0c00034000d02610025001c550002d80d581e401084100c0c0820000c90450411400820155130840b00d440b0810701490309 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 672271052 1250 672269802 672269809
    0x11042606040605131203050414030a0f030b040f020a0207060e0d0b010e18010606110f070f05060a0e040207240606081302030c10080718060f051615020a110c 69
    0x3002880600076503110404245104890b500d40700c066600040c03d45c00c048201c1c070700103003d820141d405440b020140d80341640204808011100d9411041c0c84a01e00c4415480040d406000b070400e001d907100f6500c0e2141103000e2441d00040201829660280443d40d00f041c6018204010800e141801039801d0808000004c0d00081520b065900351000c20b0801d1703449030f441681a80da84804101d4a5082150000715213400170305613441e4020003401d40d00e05502303d480d56980c42c00103200d0b909503203824440c104201e0408400801040c0842d16104444e124144041800d0340d102200450315080c015906003c0c0d2485100944082c42d2820018440580b80940c010100013001c4c1c1040c140031083c0c40c2c03620455404214030740704002c002c0c0c4030b5100148040d0016210700c078101c52003000b10301b8030007503014900c9841144409032005034549155403041140119416046a1036810100d202d0040c054049603200c00c1101083c80c180c103015982c1d40507014020078101c0700c06c094420302da00c0100311112964 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 672272302 1250 672271052 672271063
    0x6100207050a033509030c040527030c061501030c1b110420070c120c150e1201060f06020304030c0506031b07060506090c030402100f0e0301110426 65
    0x4e0704901844c1550071164085020041516070700300110021210702100346603508007070643c0c01c8080b0161170040224030244010740308211740c41c282e564140c0f0340c102c16a0082d0366040304041d00c01000c40c2e05060089400070f103054400d44980c03601d0003464820341e400d980e15026000802940f464030030015001c205440301060540b110042c00191101ca112000e600e030b17a40f1502900580200185003907180d0091018541c4c4260000c0d100000c555801107203120444030400c8200b07500c400600d2496140550180300400c55520320030070003840036105d80555440c03e07402410302944100004805180c80800002c0d44020b521907402d640042c031040021510303d00c1c441c01221001d80c0c2c5903580381c0d140e21007650300c3ca06192120f45074600104096052005652203140b00d21030644141d1718070b440780540001d980c0801c03a0003c3d40315410000c14442a8415052104403d06c10b003000c0d40652601000a825248155211824180003040c2082405992035200c0318988113800020001d80c0e06104440c2c035503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 672273552 1250 672272302 672272309
    0x91302212a0910120204060c0c0b03130f080d1406040c0f0212070804090501030b090714100f2102070b06040b06040515121608060405061309030c080304080306100207050a 75
    0x100d5108401e000540d000d40e1641c0826248a02c0c119175440c7c0303985000c2d0246451601c140c9107003003064804036041e40d20408882c004c65002d42080303040c0b1801d90310700c09051890701040300c682c41c0170f0080358520b0b8120302408503040200e82100306540b5103442440101d03100140807030b0800103981d00200d5010740100701c0d4000c8070f00c4000b00b103a440242d0b06000d2428403480c3c0c414200d0300e24003800002800019020f03d4002d65039102601c011640d1400c04c0c9801c0b07040300c01c4190b4008001c0f00101c00490180c0e480c601a000326081c00080d5401c0901000000140546882040c0d0f8002921004201040d104d85511038000c0703030304001c84800907010034501c1c000e50080900034196400403002050400007503480204846408510600d41560007006c401840228000483c1c0e0316004030307145143c54001c85204020107429003003500c000d08e0000d800351410a1080d13052244813020400800c0f0540700a62040e4016114542c0d6401c1c04400c0c0049451a00c00280454006e014140140d98505131080c048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 672274802 1250 672273552 672273559
    0x1150c1718242803061805040506010506090d050105150f0307290d02280e011d04230708060d1505060a05100207050406050402040308091302212a09 65
    0x110032814480310540b0400342c2103041c40220356412180f1041d4107400c00800e43e003811001c40c01e288203103000d030b10039104240d50041c1160881e00c018809820610301401408800800d0444c080c0c0d07580d215203003110801d507240180d00c0305000f910911400c00749144080e02d002070700140105890300313074800e040812900c000c0e40052a00300600c02c2e40300c1108191010762040d00b07401c640d01d071404080440e000c000d06020711280595a5082d1031945e0041e0a800341110040e1503c01031406007102e043c000d0f0805564459015581e4146018440d01851503104070826081e050f034824140042c01401c070010007404140304401b030b00400c03800500303002103008042c4217001020406494880003c1c1a04000d80c00141d08500c0c19041082041d500003a041d0032960207960402c000740d01c500c18002070748280c0c040075107958402c02002c010f90400c807401610b482c060140050801d04101150b00d100502d0030303c0c032284010b100301404500e00c0b20310314001c04d0140302c25a0410814030544043c03a40d000740c0c07036418030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 672276052 1250 672274802 672274807
    0xe030412140a0b1006170f0703090302010609180209180a030e0102070b07030315050103110f0d11040f3006051008030c012c0601150c171824 62
    0x1080300c4100514000c265003c00c005029152819a00104821520400f0005502040e24401c41032104c4a1140190030760544060740b0350703441e5020b8002d003207001011421507594581c0051061100d00c6000d00003c036050601d911140d082c010007841c0040a802000c07200b081d4030000e612100005a01030320349a06041c82c8010010a00050f0304045031503101c40c1000b04000350203010140c0c036a000c0d503641040500c80c40c007002d4031000114115807107102e540d82714000400c12020054150800381c031034171600c210045110140280c0868150300640d000316610800d00c0410b000b89040c20000b1540c45600d0690519440c1c81d088115540041595025003007683e52001324108100840340f81c0c020300907001c00c4035a02d5a844540e00d0080c21605900d05012940700c1169011a80540f034079445a594200284a664244400b0000703240c0c0c14420482804559060710001440c6440d5aa08481c5078070605034950690040000346442e4441409d803241c000c140c40c180307a20038800086204040010043c64 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 672277302 1250 672276052 672276083
    0x10f03150609052502120a05070c080f010e0607020303060603130f050f0714030f2806060311010e0d050d0e0f060d0c1701060909090c17100e030412 65
    0xa000340001c1d00055002030400c800c01912880340c020300e200d90000d04c451a543c43c0b1100700d00300d0f00c900c411414136407001030403c0186c460910170406001c14170300801c1d80d41402c65035484583e240000c0081103100b665140c0c0003075011000103104844c0e1000850004d94514540100012030502c0020004c010200f03c3e2030210050014404104688541c01401c40c0c40b09028115900d80e02c80441c80f0b031080c503060304091003840d030070046400c1c07075958080c10003850314020003803440384000391a1200442c1140074031400d002080081c00f61000030340c000c01781d011a02c0004000140420a9440040d0181607401c0a00d800100001003cac6103e841e80d140c11550420000c00080071003407041c810552010f03000c40c03c44280c000c0d80c1d0148054a80940314000e004000060460005009100340c00100d440403104014505081d0400d400c014400c100c641c1026848240301c0440025041010f281c3d036100c0345110002d001141b007140d0501c440031008604043c6042504200031080000003496903402c100d400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 672278552 1250 672277302 672277343
    0xe070507060f0510050306090a0803040f110d0605160503041109220c08060a0908030403031a1f02010501170309010e0a1502030307022406190b0318070e010f03 70
    0x2d0180414407074091016041081d0380260201480c00313810322a00505010440200001500b030080e245d108041c0f03400d5540320744440004c24480ca80a8500303d460700000446903417041030b00c109941c4a003000241a041c6144c145841c0c0c080200644103001d000c009200110303050b5102040800d000f01c2d0300702019520046401c100c2c5244400840e000351011a48104004091341c071a0191103840c01111201e503204155003040c2c81790710a026195500810225001c00e11035000f400303141c4904501044c81c2c4606d071021a4110b060040d0005051030b41d5410100700590a029a500401907424a41e10030a070800046850744200742425040c8141b0020b4a407480c1c0313a0071641802810034000d03006281010b0180a03489500886048006016480f980210050400080741c44807600052051032540d4040038891942d440c146030070820441104009011843d90005510407034209042c20703445400c0c5040945402515003104824001c104014045110078458103030490703400c0000000c2400c44800c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 672279802 1250 672278552 672278561
    0xa0201051606140703060603050a050408120406020412060615080405072105010c11060703050115030903110d020d02070e161b0503070c0303090b0c0c010503072a0b07090e07050706 79
    0x8003c40301c407100801c0031941e0140d01402c11124a41c0b418010b6035140e07000042141d030100c4004000c0c0100b80411108541c12408281e0b12a1180c0c03401032501d515405126440d2580303030402c43e1069180d507020701c4852420700803190001400e0400b8005820076a0b11207450340d8490040c00a44203800080f800360194228003a51100e410500810043c88812001801d540c2500c00c1c0e84880d20070000880d0559100b44901812100f2007446c0c0095054150003c0340a89031108080d001c20516680d071040400e401e00220004211a80040541003600040a403c100d0558850307069000d61000304000b260090aa03c005210103240c561210118041030300340000305014058868480414035108204500002806582c0070341c40350440036980c1c021541d400e20560f01280e81e103812070400514254000c101654000040e41090107060f5840001003050748021246500c00c0b400070000c803c2030046041035136030006c07018a4102e100c075040070744a00b45002c01230f00c10402c12900085000a00229501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 672281052 1250 672279802 672279821
    0x6131202010c2a0c0305010515090705040302190308030f01050a12031725050a030506060f27040f061e0302100807020a0b0106020318010819050c07020913140a0201051606 75
    0x60740201c1381c1d00c0c1d00381607000b454126218403480c1c443d4020104645801800030b8842c0006944d86031406041d5400e106500070304005c3d90f414030000800c04800107007010007542c401c0f101d40c01d0207078480d0301d0801000420001603000050b0003050b040c1800c0800c0d4002d650a0b40f221a0102003c1c860f12683e12031100b552040c0d1044045684404a444903507078000020132109810703907805d0009448440801c411803145500b40900d40c070b0100501d1461202603042072480a1542c2141d5030611000c4000c10151081040800c040c1036548005000c840c4851082003681007a10702144101410356022580c5a183c903400c1c54140f0605400185015108200c12010340703600ca1026004c1d541d490b00065a0b98000120010030b80e070103480c146038075500c0b404055104085203c500e42a1070090540d41c80248805401e80407a64810000c01001d62151825a0f0240d4510203101e8141c0f4058100048010f410100021503070b0881042040982c1c2d1020941d80000402030510343e12292914141c0c009040d43c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 672282302 1250 672281052 672281063
    0x315060a0b18060c030301090b03030301051f030902060f07062417030f0a17130309120206041a09130207080717190206190b0d03051b06131202010c2a 66
    0x4015101c4c10000c800346040740d8074032000307106010248040540380c1c0403d0203441d03004501c0c90301d01c1c50300401910102285400604001034000c00d1030300401d405501903900c0420105000130380381c0c04c03c10a44035111003800c44128074080200340840014108803948903a072031b8060513204100c24207406004030780b0701c000c20711703d25641c1e00e2a0305c0d0050142081038107000b00d00d03007031031000039680b5000200e1072004540c169107008403581010500c034421b200241d4103030b802440500010071021050405503510750404100c4a48881c00c40080005036600070392950400c50052014400040902090310079141d4030001501c042c9000080c0c18000c2c0c09020f05a032042d1080c4004001020f40100e0401d004840070300090120010ba040c640042d20300103042550001c0e145050200828170601c080c1010b51203d500800103210602c160a00c0c0100c01d4481c3c0508000c030803840001c00c444da0004140c2a8807a00003880180100300340906501e105a880c00002e80994600c03442d08504044c400c0e03035455100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 672283552 1250 672282302 672282307
    0x30601020709090b1b090a0324020301090501090c110c0904060e030d20072120030d060e01080307031d030a20150a0f0327020315060a0b1806 62
    0x50810601c101419582055000305c1140304200da00100f80481d820008042c12516070540745995481344d600c40030010700c501c00030340034280d28140a07034001140280f584240c045400c1d414003075070004940012a420307042c000c400390003651241c0007044c1094402800c40300680300344e9803411b00d08058009003402c02543d0200041e01c24000031164021000d10031400c20342050440705e418204107500c91480060030700420341d010032003144c0380580c201425840d1031400c1101b4840401401e1102e0703d10941d81c0200342c20114900c41110702d5803180314021b2020044070030080d4900241079450b441029005810041c00c41311a00018a65250320f040840c0090700715500c45107a07081480c51240c2e600e01030500c0280200b600404c0c4d280142000c02d04002420116242c00c0b9542803d6551100200008003803544a0360160400c0040c0140500c00110544030407010141510405040440840c665030110084d030b07040c003c40e40c0300c5518000503100300c0c0003429640c2c0d4011034003107000340c0200b82c0b55a011000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 672284802 1250 672283552 672283571
    0xb01090f08010c121e0209060c0105101401140d0506030c100e01180e060118030c2c0c0f07060f0c0c02030f1f050a09120206010611031e030601020709 66
    0x1507000110300d00d00741c3d41302d010558500510380241c506485400281450700c8501080000c490b90080c031122000600d524076250318000c24030f007075507411580006500a410820021850f08891041901c502460401d512002810321102d0724000c100d04030a5160f510f800189082c1c60412011a84c440c00801c000c1c1ea034080584000c2810042c003e13194009204250004851780d803071812101a211280c1c800c81c40c50790b40c40011500d041c0181c1d040940c4c504c0301c2c0000004a07040e40000e4001c0c121405070761041090b03895910500d154401105000114900d04000c00501998240d500700b2640c030458582e2000203003022406090031840030f4400516002c409401300381c1106040e01e8142c400e400399411080402065501d45100f40c0001d01c400e12500712601c0c401c4401c0d8031440e4003102e8070a0000f400140e40d203840b814640c2040480c00942c0c004001400b41d150005049044002a00c00a518128000001200700d202d40003002c54600b070044040b546681c001c1c00468003800c0181002c001910070b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 672286052 1250 672284802 672284819
    0xc02150c071a1503011503080f0409020a0c0201030b030307020102120d150b03010602010e0d0801030305070c080f06040501061502070915050d120315060e46080309010906030b01090f 80
    0x7007030320524414490000000f24500b010b001c0e81040b200e00c04840150145107869070b1005602c0140d0500074803508110100720284940301404100030141c0d10a42d03280440d20000d0100c82000c2e004c42c0c03103603100380280001070381c1c00920504003c0301d81070340350703121a401d90048024141c42007500780300e020b07881e00116100c0e90080156040302c00c158002d03c90b81e03941440d02620703010300e41918070011342005d00510109004600078104a44101e507182d40e0f90355a400d085090030f01010100d0b000e030b04403500340700600809006000260651410544001e400e0f5400039581e02c0203441981c48450701e61020300d03a45060150241c0084c803001e81906c555180c203161a05c40f070440384400c503010030304c0c001302e1303034a00e1840c0b400030f209850b459201c2d01406101f2004116120618625904c2c038080d440d000c0542991a414a4002440c040761040d100c40c2d00c0c0004200740102c407a00250580c1e40180080b880580c1d2151601003181d960741000a0b40301c3c8001c0049031030303403050f400480340301d078a100c0001002003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 672287302 1250 672286052 672286103
    0x1020f0c060f070f02030a080c0f0c0607031d0304051908011503030f0302040b090d0f1b08010f020f03040b07030e030310030605090f03041a04030c030c0f090c02150c07 74
    0x10446007411841d0f62026401e603005044010800010b9109020218030180a00d40b643d070440780a58000c1c2c105907000d24111415030001d5400720260b0000070602c000c25426005004505100041045c0601c03150a01607035640103078410b0034403030840b906d0100d42d4400b060045102920380c041c024000001d40b001034003441001c5100440001d41e580e44038224107486442554207590500022504d0040e03000d0802140d00300c8841e00341c03212035410003171000040d042110100f40011680104000d10b250000301821681d410800d04840d60040240040c010500d10071240d0181d403000c01e100311a218010300300d00811244100050520000040c8040c80074140b010a00311f0b842900700340410b5541c0406070351110701d081e1114078a030b4070034041031001141000d00c1140d0340c074100650600701952170302da2085003411680265100e41e0038030001e200d41e401061800300035228110007070040b840151002903035456503444441c1188015004603241d1440f02080707402c481d030030011000c44c0392034070142154210b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 672288552 1250 672287302 672287311
    0x3050d112205120d090e0a1e0519050f010e0c04031205091e0f061c0501150318110607031b030f2003041e0b040305010f0b09090c1201020f0c06 63
    0x503000002c503181c0c11040041d4044c0301540079912411010705d40750202d0301515014009089403610b5590818600120643c144600e003030b0030310302013410b0030815110180fa00d500b001c0c03102c0c0e00d0705000c10816981001e180c480c2c11943c1000c07a40029544600501c407c9000740e800052100e05012091080e2550000c06001a0b140031902c1c5031000c40600d0361006066080000c15822001c020300f1581c003890510081c10041040c1390200c641c8158194040d41225800d070010389541c510000d15106281d418400c00744d110742d141c0c0c003030341c140c1c407403500d50429440441151034451030300021040c003050b01c136480111050703041c4004004c071001e040c07802400308200d054160000a070401c0d41e0754a51068101d20700708141d240e001441c0b07014104601c00035544c0780d60800050650054174002120f04000380140300a43c01103000042d0071488a204d103040d1605000464840c88400d003d0080c0500081214480110122481d0070751913403900d440c5019016181307022103907107004a283d80245c180400d50030304c0b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 672289802 1250 672288552 672288559
    0x1211100f0801090c02100c03061a03100e070c081c05010902030402030607080112020405040f05060f0901050a060f060c022b02010e060a050a0822031709070303050d112205 75
    0x583c2ca4402e02c008456000c0340740401644501582c1000c0a01e035400038540104500e4041041c5450701000700c00510419031440f2110400410428900040e03201e030b078050902c09491040508080100404014150303038050001040007a0010500c0e204100c414110000c4c3c020500840d82d5804030400250070850301a8000d005230b00005102d0b6110700700c500e050341e034080c0c140d101c40e0200350280002040300510849500c9004980e90000c10313020040d2501c10b03d03691810044500d001015a401d40c0d0024003050b807224189074003800482d99185161003a907040303140102e01c00650303000094001100303241e00c060201207003c10102a04042c1011000383d8000e0303c07003000755803044091140c1307442454907110016100388500241d42d40307e012043e400451074a4184890b966100a44046103c81d01003100401c601000c1401118004030100e84d0050805020f00842c1740340d03880c0900359100e41c41d01e5219a90350741d1041080d01100714141e440c0210303840c04140304051400c1415030350503200d0141a11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 672291052 1250 672289802 672289817
    0xd0906030b090103052802030304030b1f080a0204091a09030a030c0503060d02041d030a0807080105090402010c1202010e160816080a030503071101051005010e04151211100f 76
    0x2007070818002050482c0d5015006284481250b28031210815020f02c0311302403081c640741a500969070809c00b600c00f65008a00c0c8420303900704085e5050021300d19607126009900c0d40c003000c206103030340070a100503c47d405940101d029406490261402026454941d40d0034820000340200503400102800011503542c5080040c1d0660010503216800116140c0d50300416000800006040039000400500c1404400e694170f03d80c000b00983c15074020052403030006220004100e503031540847e2503801008103603824841414503030002481c652481502401081c0c25112005031107200354480301c1802162020740703408d0100c40c00380c8401d011103845244460b02c540c4040c03410203d090f1404800f241e40080040005601d00da9080d00e50385c01c002c0089040c42401a00e600242c0001c0c02a0b0b88180990141c4042040c140400035011107101554035002e6850308408041404800c1400000d446604807540156205841d0043d55101409501c580103210745401c0d42005400c54060103084aa90300e841c0c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 672292302 1250 672291052 672291071
    0x10501120605030c1905102109020f1918020315040506010f1206050603010b030a0501211103070909030206010906090c09060513090c0e010305060402092407050d090603 74
    0x24141c80641c051036a0581180510881e1071600102d00c900b60307400c10000001450341c520028458654a0f602440410303070300c0610035401220b90350301d41800f10044004000600300343c0c020643e41c0b0305440341740d405141c4040e2900c085a0710001100010444220b20720301c00d940b107124050182d0001da030034541c19039a01981161742c1c074060040912400069503825528580741c4011504407440c0c541e6108201d03aa5074000c50103480d020004e501800043c00c00030360342d05021328400c080b640140e003d01d103012181000070001ca43e0702210008281d0b040344c4440107520301e4000080c00c00b269503201d86403d500c0d08102d0b04c20540c010413568120761100705c082256581e603056010996900100b103000140403008180080c1d401103001d840104032055501458607160012072046500308103002000c18108003c1044640c4c1c58040d15900c4031080d1003e50600c01044003050007013041c0360800c074009804110840810748c1c0b20f0180c8801d1600b04080f00c001c082c4074030f0081c100300898020300300007070f04184204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 672293552 1250 672292302 672292337
    0x10809060606220b0a032f040510021002030f010312050910050a122a05070b0402040c17040b04020f190b0c0f0307060f05060a030812060607060c0206010501 69
    0x341d2160101406142c9415400014048020030300d0008142918a010001c2200b40096001c0d200307940c15528001441c040d0690003800034088655044400c0030350355562180c0341c43c080195000c8400c2580d0341e064031108000207a0500d0103480c010421141f02201301700d942440b80301107a04a070b0007001030404a00c1001c804842d1403050907070380307600801c103090100891071054000b060401d41c10700e05910b220302e90001210548a0b50030b0400000360040091076a40c0c420190403004080b0141443c0d49440d089a6038076a2800c0c00602c040e115a640342c04440820b03018991031000c14900c207410002070f181625001200000c2640c05a0042542d41c92980c00c50404e040319a03400001c100c09a002c0030300d458400c80c1c03c2e500c00d010b02c0c41c3c44c0c0103240d40400c06000c100f001e0300c0d406100e85008107818540300f5010044400003010144039080c10081000490070311004c4031a40c0c409076403122015610100071034000d1184010042c41d07140741c020b4404540342e002c29840d05a0344240e0718854a9001c80080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 672294802 1250 672293552 672293563
    0x1701180b04210e1c0b090f07120302070e0919140c04020307020c210a110f100906031802100f0809010c0219020d060c08040501140112030c110306090c010809 69
    0x4400c04562001012011441d20504d584580010300607040e00e540e105a84451704618256417440407544510844180312006011040c003038105010b64001503070722514020f65480e9030b446004148902c11000c592816000d001c0c0c041d1702201500d612044d0013091a1025520241103200829030050407001e50080c034080c001c40b40258416402002c0014421040200030b0352381c0c00d01044641c1d02c5260403002400c09000301c0e034085008214000302d40e1115800e0005002c8007030707180c0c0e01c629000c0000656050b001082c09041d40c00b82d24002a84960400814482c0c144ca50030181d0700c44075445a00100035408081580c104a0964980d800c079142e0344059400d07210b4404606c009a0070014100000030b80303444080801600051500300901c00320341704c0104465000450710f0000c2c01c65010881444800d00a81e014940700307039040ca1003036240c0111303d80d8041281c0001001c000e110010308040c001c1000200181c104000c055038483c2c2404106182d482e440b5045180c0442c0e2460000b40f02c20501141c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 672296052 1250 672294802 672294863
    0x718140c070803070e1f021501080d050c16140120031c091b030c12080a050c0c040c0e131808090d06150905010e060a1701180b04 57
    0xd803182881030a80c0c0702200e03600020319413420000007101c421443e070344e1a00a024402c000f407680500164940c074009080420001c0c2031034110032800c004105910000452860055061501da03440e4100c0700c1c07070700c0c0c00d280142181009500081d8004103a2011304510480203a0090300c5404140c103911101d0b034100c540011100040f6001400310f0340070070340440790140300410110b80000b51003c0641c0e40070004104081741c608041c2c80c07240140704025a0a0280300030b0001c80c401d42c009094075075541075240c0310703a038410810481701142e07e60381c15608028481002e10014401c1c4000d003c2100010201000500254400d451040000d800001c0314403d16140101c00c40c1140c061380265151500c2d0350344a0381045070070141c04104040031541e640314584000c0c03e081c003003100305c0740f03042540000c1e2a411303008100880d8501003400309079900c010351001124030700114500042001100341d8010840307005401d462846d9281540100b00c030b0031007020b10880c0300e001100c0200c3c1c0c4e003100105600c0801c49 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 672297302 1250 672296052 672296071
    0x12031701140d060c091701060303020d0203360306090d0207060e0105090409020f150304021009060c24020a03091a0105100309020f040207050a02040e120a110f071814 73
    0x3818000f189a0f0307006003204500a00744030081036650007440500440045a60140365900c2d032041c02050350501405550082501c01903052031f03031484440c1c28000320f503411600c143e040315a22910100c03200165802015006054a4481c50140059500c03640000e0000005005820000c98140c0c02a07100e42040c40c030613502c050810300b964040c04014848640183d9025419640340e14082c0d4070351a8100060142c08016522402d107072041c03010620000c0b4210040c0069901c0901029a002e026280c41603041100360082042e0290b4440030110300c6504032010038000189655015055001400d840e4410128160045100305100d00300c01801e0043e280c0c04554800b2107030400d44250088941503000a01c00c03822101c4440000d01203070300c2040111065085103100030305511b4548208488014400060300130a19010880c0368a889088401c2d802e01149072209001c401c0c0401010300d0215a9400f01c41307803244c451064241810480407140201d40c1450025040d20740d6107290a405420ba44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 672298552 1250 672297302 672297319
    0x3110f040e0a060b0f0a0f0e150313080406021e01230c090d110111070e0a0c05070219030b16120e030903070608010906080a050c040903091203170114 66
    0x5411005110001c2c181a040382d407103540219240d0400340003040f0000443c040c2c0b582d40c1d603070144003818064400080605000e8464540b054a03154040108014401c81c1d07002d6541c0d5803848001480358101a1001d81640004200810151340014400c404400d0660109941c9440e00074010700342d4403d840504003070f0340e07200306902141d002c805e1055000b0b00d01c0c0908500303040c03009010070217401d840c12003a1505404d075103120a040d41c2105203c1d110b287c40b030003d0801c0900300406581210742c040c00c1a58041d0b41d40600c4003043e0310440940b03501c43e50003010801740f540c03800411106021940401e981e400c020300d010403040c5510ba01ea0399001003a40d01c4200904c00030b41401002000541141c041c1c90108101c11311940c1da043c0f01d84005411103403504e840e99410801d8500854000e0713048513091340e210b0a0900c1c049800050004600b85084a002c600141d0341d05d01260030001c079901030b089507001100b2520070150445854900201421a00b5640360380e10f030700104003144062019508141407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 672299802 1250 672298552 672298559
    0x210090f0b04080f0705030a09091a01050901111506040507091a0d0f1e23040206090a030b131209060c150608030711100503061c03030b0409050303060103110f04 71
    0x7078810040d070007801012804d040040d1a102070f41d1a6028a00403522900f0019600501941000c800070141410000420140c0c0012030000c0c983e04c405544c0c40d05111001c50302d2503280e841440100071902c0101c0c19212003140700f40c0030180404059803624030840c02c00001070741052056602c1c40c1101c04030840c030452840c940360981e245a100400040c400340c0c4510f440d00141c40c0c02e004003603504800303503090054851805d490340c1c215079140c94445640c4501d0008203003c403104c0000c8541050301140d54640d03807801c00c0c0004043c101c00d54402005000504100203035001405080c602c0d59000d0710507040003801c10343c400c54046226010f000045a01d500e100f60200310403600030051401000030001e0000d440301c0609145801040045070507072914040301301c2034248540307a10010081c2c0c0c00c0660550038031400094500318502c648401e1820005904000d15100ea0001048044090020000c251103418066102c5d130044420303901190501d214151040700450480d0b051048081c440d5041605 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 672301052 1250 672299802 672299813
    0xe0f07120b070c0b1801320a02031519030507290a050708030a06030c17120c070302010c0f0f0b063a03090b030f100806040c0302010c0302030d1b0210090f 68
    0xb03c0e070385c08078036a658941c0040d0801c4c4090000c010390003440701907800e030a040d414051503240c00040549088a005100380020182d003501e04010010f41203410008c400c5111181e00b4403c8010b51001d04a8420520001412520302858400c050241c03108203c042d80b692803a410144035041d070341d4001510030001c0b200401d03401400345070051100803011800d00e40d41c0d11510440c0d002030704401925500840c405011420800a81c46540c18454156050849501c403413503d4404c40c0c400641404023402d410400c015000b40031080c031a0f4090212008040c6508240109982c00c031075003805502d903242000803917030810074050702e071034000820406000302480b254183d0410010044080c080a040046440451180031b54480c0440c08020501894451005442c0e000d00c1d922104040e0000c00510010031901503c03001640e4080c00e08150104613840c00b2403852040c095668016498048a0030a0a08800c1c40800c592030384c1c1e080350480741071f200300e5008444680c000244604010010100040c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 672302158 1106 672301052 672301081
    0x6030b01081b0907052b0203040201110a020d0602160c030f0302010b090103031215092a0215150f12030406080c0408100e0f07120b070c0b 61
    0x1420b5030228030440d8001c0d050404008000410551440e080e03181d01c9160901444118640c41c00c9580030402500180c2c1c00700e00140c583d521120895000145880201d0f13002019268140d05075a1a94000c0d4401080c990604500b02d102c9070228188160f8400194010700101e0f130085920b14000382160015802c0c24400c208003c010b001081d8410300090b14074203291000694616520180030b03103204c003540400c90301d070304281e884131400c4003216100524844181080c0c42104070314000ba41c841103141c408134400c884d041e000442c2e42045201001400744003034007007005030380001c0100f607000c004100b3f000702d190700003c4d041020660013440283e0080544041c1070602e030a05030065114038034604140107070783e2203030890700702000c0c140b08851400e40114101c07400d9641c0c41c80300400031104400f00b9200c004c50100007030110780c00341e4a506011540002d11203a65500c1010b030b8a00348 = true := by decide +kernel

theorem cover : BRFrame.Cov 672122302 672302158 := by
  have h0 := BRFrame.cov_init 672122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 672122302 ≤ n) (h2 : n < 672302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
