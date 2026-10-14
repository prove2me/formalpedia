-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2195
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:33.153355+00:00
-- url     : https://prove2.me/submissions/da3ac5ff-46a7-4718-99fb-0314b9c98506

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 394604316 ≤ n < 394784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 394605566 1250 394604316 394604333
    0xc180305030d0b12030706050612060109060e01060305190f0209040212070306330905090702060609010603020f041e030b070e03070603050f0739060c0305090307030f02010f0504 78
    0x255140d004a00f46891022036103481a99148404084130041d8141241c40d21154003410010b0f1000381c2282407542ca030620890f0a001540c068012224017081d500d140c100072044410b0142d0102003094940b200348175003407180d5100700149400440011803d0051000c04030000d1043c074902c4c030b038002c3c40080c0740407500b038a1035803080c440c0355551010013446541d0070a010b0002600440f4031548000212109040c4604c22100c01c482c0d5000d1400652154031080822250030060700c001000d40d2001080124a150954041d4058041c42c5000c0d400c222190500702c5d014010303401104900c07003215828502d4801c2c140d4a050040d41c00151500b0350b8103045c80040c110f689440135a5000707004030040415403500034041d440c044c500303e1811021a6503510021160b100340410350707620030690b01c00c1c068600e21418018580c420014a204002c07100685810001c650140e4001e009060824007040b0701081e01005032441c05030076051003d0f100a038454128010074402540c001c910340f40c50140b105009070344 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 394606816 1250 394605566 394605577
    0x604180c050406050a18090c0e0316060207140409330209060306060d0b03010606050903061005030607120b0a03140f06040b0a11040b03090303041b03150c18030503 72
    0x95800c200803080c25004660074461030103000e000c10010000d00d12241d2041c86010b103982c041c1d07602d062000d5140c545a0050b604991b030000e00040c04008800082c0c0307000e014000008080c000c002d11103130310b0702c500691103900e0b52044103c4c2003d50109003246d61102e03080840c80d80c0d070140004000c036170100171042e00e03205107520843c41d08500c400328420190040c421503100060041c1418156560481040503a5000405412041d5110700c000c107102d4800740102800b400d115100c40da1144020300a15103030aa00800030720803020403480070005510081142600400c0614080010301031610035607010b4042004a40e40119031b104000040c412010714840500069501b0380d140310284001c0c80360303a03c6003030714050300303203403448012600240065024010321a21410401c0c103003541c0341103080894000319044031068000008000400c04920302035603031500c882045100c07071415500e80802c0c3c4810380340c0383c2c2082c650b01c801e10403d450240417800b0510b400301c91a80042901d0b807415940321b4220 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 394608066 1250 394606816 394606859
    0x605251b0605070b0109020315041104050111070506070204020901021e03030406050c0c0705060a0309020303030a0509070b07210e03100c11010c0530011d061c02040b030c0604 77
    0x1030101050541c410001c036181c481e0002e00d50a810307428101d1200c000d6201a003001424462101c0001756031311240102e10343c8015020501e503e0b1850039001500f004001524002d40d40c00148081c8115610002900d03001038050f02c0041e15000c034040141e140c98240324040102c101e131074000f00c16034a0008015481103100d1442485151907422080301203000c0c0e01d400c50240d40011000744900d003082400303040141890300d800f00d4000901d4012900315403081d5202e0b484a52518100a0310260030071a610042040c0840d039443d02080b900c0f07142c003131118041c8500d076000e100f101c500c140b248110310f4003414400080a541e01403480b50740300303001421500307175400c0400c00100301e4018012062180c42d07084840c9854651a0000c003001610325a20303885c5420b028102030380302c481101500141201c0c00703090381d00c00b200800401340312001041d1200900389032187d081e42e05156080d0300340990034200031f5416100450a200d060001034103200340c100d492600b01d0741c0402c00180c048220020a004a442e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 394609316 1250 394608066 394608113
    0x1060303031a0117040302031b0f0706050c211b01050a1b052a0609070f08010504020d060e100c02070302010e0f03030304150f092405060a060525 64
    0x31010128062000121102e40030401103482c0c603400c0c0003100300059015110f4410340340b07403603030714204141e28151500e03d4035002e5100300260301280204000318000b9128605080742800f44440400740d0f5103201f000161021480103081c00740050442007030314004241c046185907004c41030b0304154000c2034100e0701e100a003405c4c01655440b210911100b03c00e40d40080d5182440c00c041c0c5d09040e0104844141203440d01031110754a81d00516080c02406c2c000c080780e80260241f42d1405030140000f00b20380e0000d210f05e0b4500300500c00113a0301c0301c1c40445117590203400421036403003018030142003400d034400140415003068200309005602194034025207200340c980c00040360315001840082d1004000d003a804da401000031034081620844281044245010041114411902d544e000c3d079590410407160088100e010840108c4071701c032156540249114100000c1c038008000856400303061040b40b042c40380009071080b01c0e0100300d0f103580749400703e450000c07542c0c880c80c5011302c0203d0040d48001058007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 394610566 1250 394609316 394609331
    0x1103071d0306062b050717030406020622050d090510031b03020c0a08040e040b0105011b08031f08061e0f01330f0f0203072612090106030303 62
    0x11500e20000244001400408556480c0c5040c01500240c4c42c49800030101008840000c180601a0100310640700b800039220151401c0020168803001048004041d0010b000a11a0365800100c1c4c0f87d0214450f20b680b9030b11504540040c907868601d180141c8940102c6011503130458009201c2403c540065400c00a20301c0002011021a04054402002e04583d15248004039109070003030032010500c1c00513500389150569403840b095210b90b1001c1c0174010020100000c0c01811103100d0300400c0c0c28201603500402580e1a41101ea203914001001c60b4030200c0072501346241001500300c440401c160000c0e07880e03102d81c0e401d507035050110340402c00703600001446905215501c4465005408101c1d25286070b03400e00700b00322030115080c00c00040c0c80060081100002c4024401110f050185490f41442c5a81d0502e0090040400205401c1554010880307000018140c44010744030005036000110051488410210345125225500214020030018044200010b500043c1100c0c446d403010020340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 394611816 1250 394610566 394610597
    0x41b08030a0903150605090a0522030206040c0e09060f07091a3f0a0f05040f11030607020a08180607080d05011d0a0506031002040602160e0121050a0204110307 70
    0x170754040c003410303410440e820301154040f14590084ca40210100072032450250400d100064050f18880e4280c3c0168007135000d1109000d00c44061401602020a01d9145440c08000d415920743c030150408400f0010200000d03900da100d841c2c0c01001d000030108059110300c003074415803c42d030403106a5450081008501040108104400a02e040340c0c440b8480080f108810146050a00050805501c180c44030b171081c130343d0206c42c841c0354807940c4681d840c0014007501d13007441e44000300c0041089019612003000d002107d0b03000507106100581c8516070350f40e500c1132010011590030a0300d040341c1d040a0085103100c20080804050b00700c95500d9a01000f061780c1c2c4100810941d400d111f0720302d0b8102d6030180451300c1d402003a0001503204102508448400b40ba00d00484100e0f40701c0c1e401540181c0002c80c03241ca03200101803c00d0010f05242c80c0701e003655418001001030fa040c50b08407580f813004000720428200310b0203002a9441d0754008004008980c04241518400c0d40304844460004590a684020350b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 394613066 1250 394611816 394611821
    0x50f072001062d330e0901060503090f0703030e041508030c06070807080613020f070b10140102010b0a2c010b0a1b0b0f13080d09020315040b041b08030a090315 70
    0x88101c1c802a9552140c0b02c00c41340e4480031800c01424200f04810001c1481520740501d0b01d030082071590703900c596a01d080500340707040070a8203001e0102a00301220420109503c900c1030480040100c400183c00c0708001e00800c103039541a03000c00c0349400701180010031480041220342c803880301c0740c4400f01c052707807203070002c0341c0b20542203440710b60100c1900c159501c03032440f96010300304044260504600e05201e076145d1002061048420306524017020801384000b4001c0124514900c8080c0028440c00c140d007070000c1c001c07103000d00a014466094680711000c2c0307190802d120761100140d01a004483d6102c3d844503416a000040c45404110080d0b802145507610500303100c2e100c1d41140250049442c0c541c40324a01110107007400c1000c804190032203000c41c41c92002030404581f207060020703100080e40706040c105000d07088044410003a1000b044081a14102202d9106a000102482445001c6a132541c81c124581009e1024480030bd06507007101e400c5000b000c1501c0c042d03404641a80f810070000420f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 394614316 1250 394613066 394613099
    0x801061407080405130c1209020a09020f07150b0f0d0f060b150c06060306011403060703020a12020301080a050c09100e1302040c08010603050f072001062d 68
    0x2100d50458840c05032001001c0d003210361007030805a180c29680c100040e0041d0500b50318805e2255500c01c040079a80c0c100703e2500d9944d800040a200350300898000406800d1244180011103400013a000c440c3c03021340044038511680055101c183d501c680100340c0c02084110f01c0700d4001c02171401040c140e8a8206c002585441d1f200c80d1030b10044055a4440001c0d1191b4003585800403081c1c4119001d90400501501c1c020700e441c001464607140840030140b4044040c0c0c0503000c4541006681c0910b0f440c007051041d40580a0308015940351010b040403034604003070000d464507952004c00040380040004c0ae40680c01030003001240c104c1c00884040203010f20307082c1d48014441e134410204001480180825903807101c1519900f0159801a8001c6010f4586a1301803a0008100000600c00142c06d4402d458000440d6444800f4034031306020f000d030a00303403c1075800070500071a40c0d603c69940385c2508000094450040c40d10601e8451b018028404410310b20f071220750794421000400e405076103000000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 394615566 1250 394614316 394614329
    0x5130803070509010201110d09060f060617150a030c0302120c0f0103090c03081209060c040f030602030402040f1a10180e040f05030c0601091a0d17040819030306060801 74
    0x9140d40c5034410141c4099014610580c19075480390001c4a00440c410301804130b0b105111000f00b08107940380303060001c50350b1502c07141d00c00030314121082c450903512000202c401c540b200146245610f031351190b01407000040c00e01e90b5100103a030501008000201408008482c425280c0351882203400c1d06ca0f6032290b1504800e290000b03440c404c101c3d05136102e0f400109103140511034400b903140c1c990300d0b007040319400700d20110182c54900041c4107a40804100742c80e881012154030500b003c1c02c14102103007008192001504007500400881d0545d540d90b40030803440030010300304204a610305070030b22242e07144103945d06104810002d80759910303c1c0500c01c0c040310100c119801286490905c04c00046842d00a002a150760340c1700034580d000034000304010300058071410b00801c00e07076150002420030754007c00190b1018811810030745059450340d0404d19042c03a84003509640141c01941810018042d076880100240709040704005c44440c004041d00015010380d5052007182e481d08400c0d104050288a6403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 394616816 1250 394615566 394615583
    0x9090703050708151804080901020d110318060405040f0e010609020708160302034b0d091e0b01050901050a0b07060e030702100216090516032a11010513 67
    0x50108816000d5101350800081020f031030f00014500d0408080e904403800c0b2110000040d103881d440da01003044c60310441320352400100340c0c0040c0c3c1000c0e03100c0c068600300001c0c2190060b001500ca60341d08040d60060200036000704220b0007100040c0d0054a0f0f517070850800d6500e44840410b04c003240340202d50f440e80d004004280380c1580c004a90308484030111059045020500004920801200c10103804081c08011b2480d00c690140d550f1200c1510148079141c03a00c01c4c9802c0504848202e01a900c0704603c6900c0012100340ea0b09001c201e25020180742c20210020a480f0030802c1150702400d416108281c0d14210b65a880d00240203042c1402c1c0a44414890140304020000704190400c4088280040942c1e060012503030101d1035141c1f240c020a00982c102c00d04405404900f540e100b4024030031030800b440325050682000b51104610030000b0109a1a070800c40036803080c0000f028601d00544a0051100c5904640100055441c2c0f0150b2015401c000105240304281e038200001c66800a842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 394618066 1250 394616816 394616821
    0x10506011b020402070f0c030506071b0320010e10050c040506040315060b0304030c0510090b01051315080604030909050915180a0b10090e0303060127060509090703050708 75
    0x4094581e145a0704903480384d0200941c000140e003018608140c0d5129501c0804c8180c214900341c1e0400c61b0003401c000420034070010243c05041d100b4200d400554142c24020031481c0400d40e9020340036500d0140342820760034041c0c2036941043c00202074455a20b0584100070a4680307101031000c1e44928811681c0c001d800b4002800803a0040b011988070700001c82c400500c1c3e0780d07525000410394100320341c2500850240342844080c0a410f02c02c96110861404040002003415901c3c0308483d401801081c1c0514001161108241d5980e80304103002d1090710070000d01965074014003a55180102c40c00c07000a81192400252040c0c81d00a01c2c1c020701e00d001c040d0140d109046081d00303614070000d00e00300c0e00790b02d50b204200300800700b071013100c208a001c1e00540c0f506207000c09501d0746001140d4010341d80c003440c10001c04186000482640d420840900c0c0040d5503514040d144c40005450009011005843c04400200260443d005101c0c00b0b006a41030030305551080b0054080341c0c403c5880c0004541e01c40f00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 394619316 1250 394618066 394618097
    0x10e0a030b1305010c02010f11031003060c0c061d0d180605072a05120c0d0807050109050607050706061401050913290a0e09192102060a0e01050601 65
    0x48050380b103441080400b44055481c1c89141c00c1d1041e881a84015075541d00303e040b9400c1c418001c0c100d1000804c5442499414a1880303110034500c144806015140d907162444011442044000c000e80d81101062107244030050100d07810050105201c08140716010b00f0030501401034120780c6074000d000c0f00840400e45003d84c10385155011030011140846981404013018521000022010315041b951024540c1844144403000c00358039a865120703840b10405481580c0c46506080c0080da1101c01c0a440700c88510f403c0707024184204005080e4090582048216035100303010b001e0301402542c06011341640c3e95048401c02c100904064001001088645224107000c82c0602c050402c281d000190480302848604613600c9926032120505c044441d10720007454201071010240c0703200c11130482c0d00c0c01c281003d156903004180c114a24030720800201001c2c4560f040000a105105030380f250315000c94000003e4441008407141c00c001880d04500c019918030505c58180325032010303152081d00491111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 394620566 1250 394619316 394619333
    0x11e05060d0303152403050703020f0a12090c18052406130305120c0f0c0303160606080102030106050c0d0f080c070c17010c0f02060f0103020d030c170d0b010e0a03 72
    0x89205800d5070351141d0020300c00030591414849140e4411701d60707203884181040202650406080c103020180180070303009440002c0c0c4100d42c0000313280d08100c140c403100e48a001c0090080c091015050040f128070000f21002c4102441000e050080c0c2c0c00c00003566000844c400071000841c1512011124205018141c2005801810456640800351402c1036a0f59107452074458202c001c6140c005000c910090304400410008403422260340213070106004010110340d59005482c8200000a00e51401c0c1003030003169840340d0060309500380255035941e1207442c003601a81c0190002e4030341c0d2140721190140d55100c2c9070070400c0e94406039140f0003281c80d03210762072143e074002440a540c1c4150050000407200320884c0f5039581021100b001052070002800c1c0a81610042c202d12820f541000c02084159100f40b500541900d50495400b00c40700c9280c141121414006500108002100030030081030801041c0a8005250550814031404640d40011201203500c07901468110350880c2c0300b4800600e110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 394621816 1250 394620566 394620581
    0x507051506060c01050a0c110a08390c0f0409120e0a09060f030203120a051c0906020d05010f05030703081c0e0a080a09060e060712020c060705011e05060d0303 70
    0x10286401c00c0310f0b501c001400c46609883d0862056610503a02503c5a0400500d6041c0c030544406040044440d454103080d903c14040e08a42602500b132001c40544920b075117111500c0c0243c82180c510040c2402e50641d10320f80986402c0c803c18010b501c0714002d00d41400f03100105039000e02d80c800740c02e40031407084d40d07440341e802d50a50f402200030001140020003481190000c01ca030140040c01c0c9803450040c1401c2c100492440c46c0100c03c20450303040f0468000084404402550703482024500f03403800030500030208014010950b030700000b02d041e003454a90708003174141c1d4070140d06050341d030341d0360320805954100340d110060600d0420b01071216180c0c1c0c0c03407480c11861202d045001c00c1440f0750b90120b6041036980c03002211881d07004541c4105055202c40030101401c264104040421200c0c00080c0300790045010003425402c0700c00d40804d60910074450301e2004034001c1c28240d140c120342d2524501038403c0781c00c111002c0c1c0c1c0315807e081c1104294040e543c00b494000e860200d072195651130072000307080340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 394623066 1250 394621816 394621819
    0x318050307020f150a0c0b0f2e031505160e0f0105090406051c0b010e0106080115021204080703210e060d0b060a0518030d023004060302090a060507051506 68
    0x14010104130840e002c6006085403a041d40d211200c082c464604540c1800002e000001c500e241e49080050304065010350414908030080c0801d00100c041d2610111102c0c99080148842407d000090810b4403541010380140c1192030381c0c002c10030380c1b108101c0b100810f10700d049601400b0024426429401792005200d0040003174130120b425a1114041408000c0c4000d07500c0780702c1c00c4012032105208241c0496805802d880140c180030707501d8500d0040800da810b02035085800c3e00304074650b10080c0200b0400c0c0c40b4a0340582403a444a17030703500c0383c0ca0703c80315644000c1d5494041c0f00c051034000e003030002501c20b100c0104d849082c10345c1401414084c00750070a110b000422030369140d07401c03241e0361080050301c0e20b01c1603951041d41d600c481407000c040101100300020301a500401005410580100700d503c0079040844c09011848540d003000c07000b60403140690034040d034000034046030459050b002004038000903203529100541ea030360f0803603891007860701c00f030865040760507810209170603100d285821650 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 394624316 1250 394623066 394623079
    0x1801020109060204030c05090a020c07030204020a0309050a0b100e010f1712030c0306040605040507390b04030f05040605040501081504180203060702240702030f1305010318050307020f 81
    0x10702d58030402283e019410685250500d128200502d01c1c2007030140da40100020303810342c00d00719040c03403440e91130149010080c07080e03802003161380000384294800482e494129044500e541c81f00d00f8100e1f00c0e24020744101200d0000040d020a03084d0651000c00d04a03500c00080b116072514240c54026200d00555985405002e10022600308d05d018070003841c01042d0590425581e030400c001000301300c518079070006000c0c0307082c0002c115099800c0a00c02403c1c14004420f8002079908508162898500c242d2003070201c0a9810a0410300c52004141d505c180d120340c50307844809400c0c1d102035501c3c0c003c5209140020710700704420b0015500c591701c880d4000010500d40100d44407014001401d50b40003980f407103030101c0c84040c50010352500308815600510140060f00400e00d140780720081480200001e100504c51101c08990f40610070001c98815804121103152100003200c00a4500c5405100d40c0c0d0001c0e040c41d00380e441d101d0101869070710341071f4000300462920480d41c1c24450300006039400307642d0052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 394625566 1250 394624316 394624331
    0x303072d1b02120d050301080d0f0e090613020409051f0e01030f03050904020f0a18230303090d050303160e1315031506030b100302060703080901090f0606150c030518010201 76
    0xb1010803480c0442101d580745d150701c960500001d10b262407081d80c40361081051006064446642000d01041418802d84190015546a10104070f0105080002070150307480003400007130310803060744214020b540740d544503512050b110703441000000850044070301364064880100002100e11440410461003403c0c12410900c9100015049801444494254000000320b036900d80c0e0744a41d035091050465a05a00f03814101520a1a500c070340000c5001c1d00c00c0d000541c070aa0b50740030800e50744128001041c03851540d00d203182440d2030b1740003a40c24404100784065040326070b5015821031100144050300341d030111001401c40c8405003000145418608100c8800400400c101c50a41011040503900c0030400d20314600c0d16080300c03800102221f201a44120782800140d42d10800c454103543c042c90001290b4450014550050021000c0108994050040c81d801c010198000320201d80e400d2041086003011310206603003d058004000300040c0c010803910660030750b0306000220580040c800083d540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 394626816 1250 394625566 394625599
    0x207030203060c040617070516030e04020a03090506101409061f050a020706080c1603020304091a0901050f1f0215041b05030a0b010b1b0303072d1b02 66
    0x281c0682c0c0400050400240c280f2006400900190410545006d400d000746089440142107010b014101c81d14110305169001c281071046003900b50740e4000070300856984400d600e001d4020310074280d048031640076240002c2c0445100c40440401c03118200c180c11000005a82041020368002780840d60081c0000600e0075a02050181c4903010055a2141035440740365802c0a03250984a030700440c00c01c402c000401001d07850f6101a0f540c00d0304a10746840205009190590460003550400324031035290000344103c0d07501100c0017424859094454064698840d0180308040091030001e030742100070032000c09102052000014513144091040c5d0700300c0307040205200c0199000392410b4800302600404800d1910305540818007c100407002001c1d21045681c030034021207014810180850004600076034002c40e01300000c0d51445081d01561307520710348104050004900c2d4030441c1c64812840c0e00c540307034034010103044020000907911a442050206040120680d51000080303805c1104d51040b01c070f1a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 394628066 1250 394626816 394626823
    0x20304061202031b070f0507090e070302090c0405031b0910060e22020a03020d180f121b060203040c06080105030309090a14010623040f0608040302011b02030409060b1e07030207030203 81
    0x5c0302c1c030440c1d55400b01e400606046240044640100046c1b5180c500c241c00d900030006840c4c2c3c2203da040d0340c10b2000385e030340a035240118021680032a405000c1c0a690b11075180031742d0341c2c141000000b1560409035840352182c0070743c401818054070000c11304440848410745041d4202c10503148100000820030070030b0142001c2640c104005001c04a0b40100d40b42a8540150150700107801c1070000070440d8840685401180a031000c03000fa007404c890307034400c00c84148201500e013920322200050983c0000c141c5800300084d4022107090f140c560692101040c110311034600d41781241c200034001c40c00c090b2144200120000f0181628003a00e80c3c5071b89000322070f100558880c0c003d0140b0307110040e08205425140b054000c03c0c0300c0c41480140b08002c203100500d04c94656005a030054035014245aa82d894141d00410303080040151054241d000c10440c9540000100144c0e404928140140e070754501c1d0804e0140200300c5080d9402c200c1c1d0b00201d284030344600107400d030b55000c0c0c8112032180b40e90b071300440d05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 394629316 1250 394628066 394628077
    0x4090c0609090609050408090108041a040b090c0d021e0103090c0312080c03060105070303050402011803050102090f0303160602030606160501020720090105121609021306020304061202031b 83
    0x8100200801c01070b2000303900ca403800520441d403043c4003915080c0c0c1c03102124812a4441c0b8180200d0401143c140300c0306001c0070325000d14010750700d400c030300b0241061929a01c3c1111100450700c5a2005100c0c2c50601039241011540e014150340080750054230025100001d13100454101744d13807000b1640204184a40c0a40154040c00326041e07050b90100e80100344c1c02004081035071a031401c00038041140d910130119075040740c15280c002125241c030301c0101c50440070021840c10001c8905e0001c41031240660040c051485c0868105184d200041c040c1030b101e00602040c150140c1202054801003021030300110b07840a4003e006902d081d104050040c8000340c009000d5802e694081811f00400030f580305040785245c200b900700350078190307110000303148080305000c0c080c09400c0780452101790403410424403414662082d215003040c2d889102140003900031103044905605440300005082c0c0c004800c450561301c03a0b81d924068166401c6910020754000381c1b02031408034101c00040305600b0218040c00c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 394630566 1250 394629316 394629329
    0x80610020d08010612240317031510200d0e03191416060504150804111e03030a0806030c041104090e070504060303170a020f0703032301181406100e04090c 68
    0x80102d0a5088c5404401c4002d01c0ca403900c45820800e0026240e103044d01340e6074240c0210f90002101e00007040460f4511501c5250000140d21103000204105010a07a4601410b050740e90300034145141040580d1212082840c0001040403081d06012400c88003c40d840281e081003210b0b04810020254060103100380c0c4480e0028801160600506540114915000050349440c2c4000e003001c2c0c848110a41045401520980c4503c580080103542d5080c4000f80210040c00ea079102c4807041005480c001d8102c858501c02d000d1500113006503d000e05c40e90b2000f03003200d00c440b400d10b82401c2ca0b002c0140400420241c40d8845c0490020301030390350303018600180d80b00e83e840105070141288802c0c41c001d0040c01b66800d59006021104d44418403100f6280c00c039416143c049004028a180103122100d511010440111008004200740e00300d8904e40c41d03141803000c000c2000322208001c2c400800310603140d4591084048105250440c0308521440d900d220050001902c104599100078042c03035140d11a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 394631816 1250 394630566 394630631
    0x907030209090f0609070501050d0c0903080318070510020a0f05070305060420041a010f1205090c090a0905070302090a2a02070e10030221030a080610020d08010612 72
    0x514260009211440c2c0111700400286401e908040018015005044030324a10b0703135480ba00713511880e20440f0440020b5822054580d07a0382066010244000304080b605402c0c1c0c4546200020241018001c3c40446000c503806400da107403240e44c522001c06032088054416210310040400450014450f10740160f11039280454541a00c2c1c00d5035100d072081c184030502c03da2500155140091260520145943c0246881e400d2100d050406569410403402041049031501081103801400003540700700400381200c1c44c021a98800500800303840b1810001811900041e50800060900321110350700180048000b1070f64804203070100007444025012050300c980c0ca102d07000b040580501064016201c0780d145207550b03103442c0c038490320401c050b032100a010b0281c80b103c4603140548204030210715004030080d01d81e00c2e40e034210000c4c02c0c400e0540c3c0b01032203903554060129950f0700004803000888019180d10007242c1c41c0490980b08500031141d100178240e00d83d840032038000d02104445115a1001402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 394633066 1250 394631816 394631833
    0x506030f0907270605190605090105070611211006050d0e01090b010e1003260f0d0f0b0d0f062c030d0c020102120406020a020a020a09140c04050d0b090703020909 71
    0x90500313842082c0e000324041e461500d1600171410b0403201d95401d880070343c1005542c81c810080100d83e244507402001d00807902e230a0350780501140c1d070401818182c2000110800c1181d203080041e520520554a05070b0040d100c48042080300e000d00060000c03880031490004000503410001405e491003008110380c0310201e6801409240905e800050304001010300c00d09005095030f0710805041c0c224403200c036500c6911a0a03d030341305c070701408480c000c401d0321803480c0d201d003404000700e4050642894403600d00c078100341c52011300b814030a0700315686a4110f003914208241c0794650100030183d9103090300004a0089200300070303100e00010600800740c0c00005582c0c0307400100382e88003141c20306403081c411a40100402089148100d0b1440d400903000307400180d440200400607440c0c511036500080d040420540f000034250050380c4544140d5004140254250303440e1008074200744554059641d0110b00d40d140c10000c1442140c8066201d0641411540c80540b6600055107001d401c56117109254442c1d02e9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 394634316 1250 394633066 394633139
    0x15060902160201031a0604120512040314010b0d030f0302070f021c060e060402012003070c062d0206150402040e0f04150b030c0d15050c09040e070506030f0907 70
    0x503034480782901541746003641807400020b8040c1c89103108805104017045024428440e050101003000d01801c00c51a5549540340fa00d410310814051220510b5403a10071798030b08604040ca100300340141e150303481110101e600b400a8009410507031082e140d243e5488550380043e115000c1d83e0004103621003013130419041768a04081590440f0002c005a038105109010050340c10840300e11102000f04d00c040354001620300300e14650b0050b0840903200341c51413000040c40d96000986072a542c2803166160b0680b0b03810013110031050111354104030040e44500c00140d60103030514505500c0c010020030241c075055450030129000c86054801d2401c08011074140003c0002d04d40c0c800800d4003100c18144800440768000a031214015091607004003540c010100411150848500704800c455200f0401d500380120f0425444e004040d00a000354585007200f05511000a640c80031500d000700b82c2c4e451230b0744001e01d117a079405000c3c0c500f1401d486100404200d1030040d07040c3d103025070941c8460102481030b43d00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 394635566 1250 394634316 394634321
    0xf130602280809220501060305040b090109120e040906020c061509040f110d022112040f0524040920091815060d0f060e070c1506090216020103 63
    0x35140c0064403504110900041c0b10b4025114590001c48140d0684040c3c2805101d06840000840c00c41c0e504d000b00200d0410b030183c0c40741c4d00071406444021180d40d00d20181508071a40340c00050618207030300c0030016000348946544144140d0203007011511117100c3e41d90005a070400701c410902c3d42c2002d0100481074211090141e00d0030012511070034141040d880d104450f0003040c0700601094050001180b0540b01e041d45a4402c0b036001c2d090341e0494000340c11001d4940c2d160710103101c0034003644546100c002600e1040e01c2c103445002802d00490ba03d0001000b540808071480b548440000c0920155031416540180c0001c1c425480007081b035a2094620740502da4290000c100f120b0303000d000c07100a940352000c001040000c408070941191712050450729140003c0300c88180d00000014080101c041141c0000c05480040c0000307000c003070b031a111410a40d200c11510750b80040c1010106001042406040c2d10301060401800540035440b050b403202643c0c415190040103140e05c0c0c0c02e007411964980b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 394636816 1250 394635566 394635613
    0x20d0b0123030a0b270604020901020d0e0d0803010b0c0114070c0f0615180e0c09070c08190504030302150105060904090c090216050f0f0307080f130602 67
    0x24600100d1030210a441c80c41d0151030800034204000740400020303860041680445050500240f1040001a0180c0800945031400032550004008040841c1c0c650606000382c1e0500d05050300604003200807103004a6100604001e0103502451000f01000800c0070b00c0c00941c041c2c80500a03182c0d441c20041081429101000062191464020204a40c0c40e9002402203903180e8016161420421181801009030007500908a00840344817400107075031054515034980c0c403e080f10144091080c88941d80e45501108007002c0d00b0140c0d03680003445c141d00c0784c203009501070b104002075410002005448000190265810004180c0004060060640400c107045101c02410b529040560410003c620140926441c40c0d0069480e0800c840401540d0700741d100c09821a183c0464481e0003a2080d08882030441c541903d86000362a50154281d2000c030302d000003400d50f10300442c0380c145c8982d175400c45d41d07000c54903c0403480028400303001c8000780d02071032900501c0964001c006041c510301400051042c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 394638066 1250 394636816 394636819
    0x12170706150b18100c0c091e2f0c0a0312110c100b03011e0b090f0c090d0c0b0a030507080a060302010e040e030403021503072312060111070801020d0b 66
    0x24003040b01c4140f503030141c003102d691050701d036065a0240300c01c00340d0710740313540078001490322140c03080102d43c0c03841c0c0c0d0f44529902c81a840e5060441c90f61542c0c40811a070198442c454248000c10b030074525041d019403620361940c00d440b450341c40c10017020b09803402c04884202c00c030002164001e92040c2c0c22028080d41c20031320301025926142c1081e40100341c1e07695900f0f4255140258846502c00b02e6640d0a5200141c1841566200384001c07807502c01e541c3c010035804941c1481007003140f002c41e14841080041610817a0320f51126490b01c448103007007010140c1c121301c0c100c03580d005140307000c40c07035440c080c000e0102101d80b52000b00302c038200420041c2a48000521071051186042420030160380d000781410b08086040d5000102148919030036030940c425500042e400c201c0750750018540712100f400941c402d5441d0ba0b46c3e032400504014510a9035440003900310340180c001d00121585e42c9103c028250000d005040025440344a8603e46040010355840a04180d5022800500c0c0070710602a1340c600640 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394639316 1250 394638066 394638089
    0x601301104081e030d0e01060815010303081503010f110a020c03120906031f0807060e151213060c02030405041410030314070507030b09010c03151217070615 69
    0x40071455691a4852030f00ca0803210b03031644210304841c0c0c0070700440e0b81d480380000040c004807a540194501810061040b075000c1d104070840804200f80f880c0440e410380745d00daa40d02403140c40d008100d000d4002a4119250302d0355031040c1d0b02c00b0002a0303200f811080c610600a90b49c03241c0e115203000c1d04194a0814882c00303a0080c0c1101c4040342050021074042c90000c072010b82e1280c40c2c810407e084005202e86204100341c0380903022941000010b841ba0494013180e49101e0f0b610a404140400081501038500c0750460512012a88001500203540c3c00910080d00700100c140325250f0b00203650a907014030002da0070000c2d00740140d050600580124400000500042e030600d40c514110030003051101400b0071042c00f00241c082004103003200c40c840c0d005030488032040e1726400c0100441100b40d0380c11515610300100e4445882c003d002e8400310b503004234980d03030803180b50000807107024501c484200d5682c030080014042c80020744c00901040c6015800004c0e135030080080388070481c0403d0b00003840e1602c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 394640566 1250 394639316 394639319
    0xa082202030601090213050306010308040807080c060403030c1e030e15120609070207031b090501050d0507090c021203010906080114090c010f050d0c0f02010f060b04030b0601301104 80
    0x841c0010100d0449801507801640d520008400a607219244e030401c80d450701411b4000814072081401800546056106440d003407640c0d160720b642d031790082403810fa400600c00c0c041000420701408142c0c2d80c05009508585004008080c510806c0e002c8140c200c01141612490359010b0509120104002940b4001c4900c5d040d200c21102d0507110004004602c180d45910004907131500c01d000840003554041c031081e62131074070720103001100b041c940101e0107031038075240c00041d59203040283c41c14400c0d08480580f40140c2000524009842150603520661040d5802c12045100c454011402010350040c0021058102100c450a440c50624600c0c090741a001c18820140404680b2011001090800071058460300c40142c88078080c070b1004030412880d01d255203040c9a00190381003041906640204140d070301641c1c880c0c0840d5414041c01d040440c050000b800020312030701803d40c122005042142d4810524a5548615030707030821714549928103620a062406814020002036030740801c2c81e1030409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 394641816 1250 394640566 394640569
    0x221070f140421050d0206090c09070e040c050f0403030c0c0b03040c0e041a070c02010f091505031506070f030f03021e090f03011b0210091a100b0a082202 68
    0xc2c0514010320204141e1641000000d241d8500c0024803070b9444803d80c2d0b03558001020107501d400e02101c691106000703148640002c1e1412600300d40c401e03541c5850340a6842e0000f41480003c00006124805022042007400d8074404003001400c000e5102c1d40c2c4640c16561185010343c840a171a910510038008144103200004425201080584501c0a414440ea03907481c00e2044800042d019040b82240c011030a000d00c2d1a80711305460011400ae8a6040c4000c00100044030504203911429a900d2500700390703071651a201c0e034011600907035000440841850300c1d20005030280e202800c02c888040011038801e007055000368540c4040d21041c1804c5041040282c2e2a01a000c40c440009242e44400076a40d5015626124401c01419026000b048280102c1d02401160903c601c102400b40c400c2d00700310b07009910315005901c0300c640e00c10085c003050381141d810500c1c00c400240600c6580c841000010840c151201c015001c0e14102c0c3d617880c0d5490400c118041d0244410b0031a440140e0030f803510b4035015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 394643066 1250 394641816 394641857
    0x306090c2d060d02070816110307030b07050c0c090106030c110313090203092d120f04090e071d010e01050409051203180102040b1905070c120201030221070f 69
    0x207034142914416a0b400000030040001d200341c2c0802080503c01041c00c202c007440c0d41c00710240c4148108540e200710009041019501d021a103c010300242d4840d00160307003d8410300140a51020101c11110500210030000c1d800c50303026040b100010380d03914890034420358081c0c080907141c1d512401071442d1201c101220043c02d55140145d4070403e0700040859030303000b030421a0300d072605c1d4003030b03403680d26800903a108215488400309844454031504031208441d000c00f008480f250707001c180344140341500e8450100082e1860260704046030003504000244500a100320500c0b50020042158013981440321080243c24181c002600071440c0024a4001032400105450104006500d0320780380d9451240c096415000014041c0d055400405c00091180b5900080c2480f0b030401c45101d14015200d680032240c2c0d01441c0005066402030a90400009072071100042c0051b0040c54090324045c0100400300c160f180d10303106030750200034010800003015400002881f4800562408501400c01c5501700910f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 394644316 1250 394643066 394643149
    0xd030b09011d1503030304051b030c0a030b1510022505030303040308180d0305160e0d080c03070807201f120609050106170f040f0b0a0b0306090c 64
    0xc54103a0000403076840f010074400030015040c02030449680745801e241498170fa003205114000d1005d40d180e04086945400300d03c0740f642c600f02500403c1214a161250b0a8980014205201d45e415180545180c3c7c1c41e20003c0c104100d2668004041d20ba604080c1c1c810394480c00140d81518001c0304105200c15071300070040342e42017a0145450744940d00c030200d00407001d030f15803407074807440f403158100c69850b054140e00014450741c1010b00d0307252424a504001c0c0d071911a004c88907070b4002d0040c9004400180700b84003030320865038980d080340c0c100840c03542c4110350355102d00815981815001065040036165140444010805454500e03150f4031001c60f030900e051490b140c0005001d03141010307802440703040c2d0180000380140d03001440b00f565140307409815009804801c0c0d04000001c0f001400c00745561703031114001c5a2004401514008030f2729541d00d8908040e01100e18a40c0700c0250039201d035407c00c1040d01070740f00c0700041c01d0900b01080811001120f4135040480040d044404203c4c00e0b21007289064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 394645566 1250 394644316 394644359
    0x20f040503070b03100e04023d021f09033002040b0d0c11030315010c0510020a02070807030308010510050909190b010219020d08041809021003021603050f0706020c0d030b0901 77
    0x101c044804801404040e400982c2702100703070741038802d042403568001a4a1300c40f421060011032410800300070070050f100014800f03008512500025866206030701840242202e00c1004451044c0902d08200f0981c2d02580c0241d501010110781012a0f05061150750740480081c1070424040c1c1840b081d0a8403030000030030601350f01409081a1840b41d00941800d4282613014040e10b042150040041c402504084065401403240080c085400000050f00c0c5003500d815886101441e803070300c8100501d0021503160281041801d10200d02e864a0300c40480f8000c2c41600480380142602071310420403290043d20950440d0700c40c80c0c244100007220380000d0403054060303600710540304103414040c0103441168083c1c01421813000f00a0440b440c544e10200c0348900c03c0700c100003c5d80c042e140c1181680140862040a002944503000020b80903400901d00d503024030311103d00f8654151140c000700d8224041d680304680006005880c8558940b20385800554212008000380d4140207105409040103080c0300e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 394646816 1250 394645566 394645609
    0x406110a150b031905010606031103011802130302030a0b01090b0a030b06060c0f0a03081501030c360806010905010f0e0106030209010c060c171612020f040503070b03100e0402 77
    0x8400549090081c200d04d10164414010303c0c0c2c00c207281c800d00038140e51003100c00217898000388004484004d0101d90485101c03241032120182007401c140c00940c0300251b0030180342c02004002005032804c0c4007045038913004440c6042558904141c0b0000d5881e55010284200f42d10b8070288001196404c0d01790f0020000d0f100c168594100340120313440d00408960121180c030640300181c0806500c8403009101c4d01c8812002107202d40040019000e6600c414159001b02d020b101c0a500400e00c4a40300300c080c1c400000351488507140003c6401e02c0004a50050103d40c1c100f6030040c440a94035018803401400081407645100d49001d140021101040c001c290070190000360315400c40c0c0c401c000d183d1505030440e00401c0302c00120070010b4001c603491140c410340703410400005103221000c000d040400400b1030321600d66401c1c100301c1d00300007503004030074074580c2c98424000030030251810020000503103000d0740400c1d80e034107018030709180a05055109000000040c3d0401c40143c07107440e8002500c0c002e16048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 394648066 1250 394646816 394646831
    0x6140d080c0102070206030c040612141f090507030209190b0307050a09050a14090601020d1b1403040905420f03010924050903120405120408030406110a15 68
    0x78068811300b07402a502003400b0090004041c1d140d002003040f2422502d0f5001d030307421180842029100d5005030601180c0031100003074042066001c3d00020218022002c400c4c00ba1203000310b80413500d00307507030b140006030b804a841a564200076480e603021001d00301000b0403003854024503030590300c80180340c1002c028010400d1003038180100d42e441c2c081c10000340828142070711055100070003504019120722445440011410f03070b50000c501a010b00309195284244003910748000b82094002000c00c540000d80c445074020070380d000703102400c080c0c40c08500101e46c1d4107007803407641c1d107005001d03107002c0c0c20203010b5401c0c400881c07041900045070088003a140c0025069400014030240f1504441074155013404041c0c420017042e000303000211074103100c1c416218254005203104580084030242c1e466030040004182c2512042c40c0540d103d4070900c11504412803448411115401035800207510790300c04501800000c0e00b10807960b8000c040d40740200b00c20603598075114148a103610301c401d14a41e45001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 394649316 1250 394648066 394648087
    0x304090b010513060e1008060d0b090c0a290408060106120f05090604021201020f030c16050f0304050112020f2d0a09050301050a0516030c02240a06140d08 68
    0x2900c4800700d648002d042c0a540d288000b4100e40103e4030506e200d42c0900c4190040c4a00a0000c903000e54005010207040007155586d40d03648240141c0820024803400a640c01c060382c50302c0e41d0300050b20f5100c100a03550f55951098178880d035100a003c6040c58000d03c000e01a845001401c181150140e10b0600808420014000014103038880110301c22400c0c8003c03c224410001030640c051b600c02c1d01c28245800c034010340c9078201d000e0280800c03443c100400c0410718a6040c50003074035490f64540203541c0641a190b81d441d20340560f01550b907149401c0880c0030402981c012400103000150031074154a821100702c00221035104100c40c0c88142c482110221440d0a01428009a41e81c0780b440d050380e03101c0d4070340c1020382600010f10607588250300b4200011309024050086500801aa011240950070f00d40303010740103080c441c540715045110703021880c589550000400c64004100d9146291a0300f42030451905603040c5800c40c424003100d40d01519208d031118140322011030707003061455450307007080c52 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 394650566 1250 394649316 394649327
    0x6180b04050c16210305060907051603031d0a03020d2703080d2004080c030313050d05030c0105011d06040504050709150b040b1314091801180627050304090b01 70
    0x8003160300c01252013411024039074056106500030041110390001070b80e03942c1c502b1221071103102c0810841d040b01c049100000303402a0482c00900341c2d6850280c1200003800d0f480c2d0315004c1d003d4410340040e401600c0100d0760907000310804107000a410f408000f00005441450390000d02840024074400001503003e00c4082180d002c1e50704001c80b04540e10001c071503a000704e40740383c01c58040c01c202c0b40103051a0101503d800422500c0e0700030402c5000136a1484d01c0204014074003960f4042ea6240010000300c0c0b902d240a124007400b030b04021508000841c440140d5280420008000c40c0c080c030314040070b0201040e4009242000c54a180201003021480c116800070205013541c0804954030000c900032556103400009007100f601c400010b204281d6880060304051806410504d400109035400310b28545c2456002c03c0100c0701c0c54001103480c6040032014102400201c406441e0745640340c10884840e07a0843d02404200d03401c0c040c40916500f1501e5080d1284224816030038016034540508540da400741 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 394651816 1250 394650566 394650593
    0x1608070204060e061c12140f040906031e0309210221010507090f05040b040209030618010b0a0503060c160209090604050c1203070b0402010201060906180b04050c16 72
    0x81d0007400380c1d903603071800d0784241042900c1a91140c4003681010b0165000e0303102140e034141d0800814040c9034220001520801c21013081290900810040c101c00200041c00410007003054400010310f0519504200e002c150003072076400d0b10402000503400c04280c1c807041d41d00644080d034030f5407950782448130520350500d0703440300c1b0094000c43c002e42c00046402c0b41208900080101d0b8000b8066a40d03001022a030701c404c94060b145802c80c0081083c40141400d51001c1c0008c80b024100501d441d040000080c9022000c81e81050a174440c400402d558503401c0c020300c40003000030b4402c7c906103400e140000351110401441c40e1030b1003c0c040f03506031600c010a58011025034014010f03141c0d0b4280f02901c2d0340c0700ca00c2260700396492300c12004a21000d0404005880380d0030718241c055420714013a0f54800c412120007400a80c11503498500100d4070b50400e202d020000d2200c80444c0c0c04465000c880d0f401030320640c41d10140b10303503c0d2104104510081d40d040356110b400490211084605ca880c260340614841d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 394653066 1250 394651816 394651819
    0x3020d240603060204150905100509041d0c0f010306062703060204150f09140d050f0111070c08071d0a1b0806120d0504090c03020f160308010f0b16080702 68
    0x1e048001080c0b01042e03009100b0f9550f8070188985100540c01d041c0c410317003254424641c00c4446107410701c005912410103002c07002030080001c98003c005e410580d0b001585200403d4075608404040700036464200780280c885003083c01c0502c5803a01c2c100d40589041c68000791280d540b0610511849240c0d40d00c0304403005940c1c0a1002c6456a84039194a078210103c0c2400b83c2c041b54006651f685c407640103c906501b01c4401560310320000c1c01c0003081c0070079001d05020807a6a031181502c13540d0001c1003809044a41503007411116120300c0746083c6210030390038990040c1c0c91030300070360400e04c00725403480203e0043d000402682415500c50207a4031000b44011a407820b0b0042000d40010403959004c1d2400307008940407503c80301218800850b85032140460401c3c4004035200f000100031010154001c502400e00d207007001070903c9030929802801d03070b0204600d032400740000c004550405400003030b001c3c01f40c000400b03003e00f00c500f00501d8468512406011402c0c00d02c03042641020000075008450701142e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 394654316 1250 394653066 394653071
    0x309031b06091a010f1202060f0a02030c010c12060e090a23030d09021e1e030c060c0114130312150504091a0a0b0108060f0f060708030105030709020403020d24 70
    0x80e0280c030703d00014280501001c0c0000b5a000003103454075144100c00c3c02d5001803c452a01c02e05004500080c0d00c1b494030141035010610a8030380c41c841c28072810341301450a031180142c80c0c26412086003101c109070000c1e404810010240b106d2a4400101d00c002c1c40c0e4003074252050501c16003542810b042c5124509409417000003004140c2c1106600500e044030310a0750501400000d05001800d8003480c107007401c0d000a0803440007220310032811222002000c02030295164a0041e101140c0c080d071212442000310380d100c0340c1a000c500c0302104090303400072507000941605040c90b90001c00c14502c1c48848111541c1300c40504100f806403108002c0204001082003140c141d546c5042c0c2c845201030b004090f100d8100500081c9103451500400641140594840000343d54043c01c100d203054418501c0c40d08403490381c0440000d611a1002002c40310702440460f900e9614207003c04d4a000346982040c190f2500601c8208010785610110000c050782c80300380700c4d030241c10381001c0d001110050401c0505aa0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 394655566 1250 394654316 394654343
    0x32003100b0a0e03010b010311090d060e0709020306090703150303030c05090a2d0b0904090c0305010903051207050708041401020a060f1a09090601230d1a070309031b0609 75
    0xb50806003003d010001603000340075a403481d40065088480002005805110401c0100701c0c42c40c050380c1030440d103031294000041001008107960f14141c6180c204070741e0303a98008148036403894a600c006d03074000341e5490300384011084100701407108581880021f0506440d08921245a8000c2058a09110001c2e0503407040c0c99841b190300981038450503d03007003071440940c8031028140d9442e90321700a86d001c485200d032601d28a09c0c1880020415031a0598090003000004070008900b130140c04011030003551107540329040b0070032424884602400030414010100310020015680c130090340c048410a29514074450704200060303040004964000380800e1900032003081c8074603d5400542e444c4c00ca10112891000b044080c040042001c0d508104158040b10041144d804150100c85d141011007a162613030380ca020011170714080c10540300f105d100c584844209000130a1a10442d440a5186024020342c00240c07005030582c01410214440201c0d000e00307541c00c0c0309264200180381c6600000500c001c0c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 394656816 1250 394655566 394655587
    0xf0f030804020108100b04060f170c070c060c05060604050a0b03060106030e0d0504080307060b060d0203010e06040c03050f0423060a020a0f050f030610111b03010b01032003100b 78
    0x3254111000c0740801c5030540803d1000210504503000c3c1d40d0a0b8480c03510301428640b083c0c802c01c0c0c03884030220401080c40c40070f110954180951502071406600180d84500961074000c0520308141c001004005191500c0f4006c11800201d05400c100123640000c4e8680f0b981c0c007203102400c004048280c241c4118030000940c40c0e0315a100042e1108050262041c00d09800b43c221000c0c07045100d542d10541c401d206080101d100369000d480315100c0200501c3c0f404c031240c02028142d800c00d0307019004c821400e1081103110f06060088072500401031034108260701c3c000c1600c405101028001910558202e40100e1421080c40e0288a5105029040b59201c0c40c2c142d801d00040d5000c0f120940005000c041c00c10390b1140500c05880144403210a014203654440040c803131141c60b22204141001045080e6040d08407041c81012191071080b84003503550643e440600d401d640503000305904152815100000d042e601f200103407903100400100580c1c0380c03200e00100c1d440028a410441c02c00700001000641c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 394658066 1250 394656816 394656827
    0x30b0a092003070501020a111017010902040303090509040f060b1c1407120b04060c120c1101050c03240409050f1e060705030f07022a090a1104050108040f0f03 70
    0x1001c0c00310200c4811031340320f100490b25100c01707210042010504c40c1204400b4038240c0d03144a4030341c2c10b41ca480001c1160f003a6500729008800c2e03211110072640028140300f4142e22000c0540a408240da000105081955980d50502451600034040350703a542c00743c4d0b00540e1500c0d01e49a4a49a6000880d2000764a040c400003400414074005054440c103507000500e50308000052a5031a0401c81111090780c1d0390311440c02030071148280c00204a04080341030090072840c8151101c1e904190380b1082e81c000c610508508441c005084441c09031802e200b00a5808803001c0b030450340e2412400c0c0088100f0741c5502141c0505289000100240030f1404212a4039000244203000c40202c0007080800102100c451500d03078006941d0b44000030030400009404007407031051560021206d00c11100e420b41100402e014a5810700490007201500860b8030303400d0300d003030040c082d00050414000c00244a141403890990312651050303078184001d680c002810301c1200584650305a8010808007541c04492030010079 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 394659316 1250 394658066 394658123
    0xb0301150309080f1b012309070506030711010506010c0203030a050706090c090203070801140604090b0d060f0204091109100e0d060f140a09050d0e030106090e030702040e16030b0a09 80
    0x212a20f107007942c0420f4030814043c004c42047c021110a40e840144120020301c01c400811041280c800d4400004e49034482c5802944a40419914802c0c480e07010900340742075510103410315040080842c0000096903012003142d8a000150600329601c0d100d606d4072401500405801403c5e02c00c0205000404034801e400a600c683c01e10399844805a072240c10404400e000c0b1a819604108140024030124600d03900c1071019840040c01d01c01c0200c0c15685000595031846040c50ba041d802190812940c21540516034441160b8844613040800210110704070500111f144400c005d10111021781644442541c5140c0c25041003041c000c041007903500602516101102c074031140c40c030705e00251550b50280b01c5c00060541c40000340000341c1da54042142d0b103101c0b0540882d4195a5070900142c145a5482886109290302c0051501e45159004000032205070350108695034201800ca089100142000001900c0d0710030301c2d010217500d480b000117008000c1d42c580181541c019400717a410640701c0c09941c45 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 394660566 1250 394659316 394659337
    0x12151e060e030619050a0603120c02011806021506120703030305010e01090b0d060e0c032506090b0a03050408070821220f0f1e03180b0301150309080f 66
    0x8000800303072014156681e40440d142038038001c2c0030348410381a66151704010b070080348400b40480d001c0c2d100d0b150a04210700361040c3c440401d00c1c10080fa0215600724901c41040090030700c3c114440b62802c01c0107900c1d400311f014540c00c0c5450400004180b5521144d0604200081808950f0459141d00c0c001d0020b2500307002d0144150850350000a4107010b602540901c1c0381d020301005240b020355603852000c2d00c0175083c0c0b64124018810f1080e0703551000c000f0240b12030382c204404d91031003800c03012082100503117400150401030200d07403d004070a420700448040a50b40d01d40000c00c0e54507400c100f011030240c140001c2841000091804c007040260320100b40c01c121075905020300c1d4482e490020404041c042e00c01d40c482c00111500404038840c0d0300c00c904180d0050490640d86082c9650b0011152080e00140c01c02c01d900035a400281984514030101d000310000e05040c1007402c180080c20b050105100b807200c0c0284420845043d81d1090300840115a48003403081e4482011114280c0503070464801c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 394661816 1250 394660566 394660577
    0x60c04080115050a03060203130b1302040b03030c0a120215010609090b030d0909020901180b03040b09031e0313060e031b01091a0903040f0b0307170712151e06 70
    0x108402c10341c180c0d12040302c100030500c0014600d0b6503116170107900000d00820001041140300000728958241c0d840c441c4103007418000c0c10614a10410046030300300407006010340d0050207048690400001c1000380b21340c0010541011500303010080789090084111340241060b52800080c03520780021030a801c0d180e01020038402e40d20000c007410b0f560002003002c40c000501c001d41c1041117412030340c0108008201071400c6800141a03420078004e0403010390013203030245000003c010600491104a07a00212400050b43c90400034806c2c0c048140d06050180e10300803800000309000b03545000d161010749134840e1080c48006080c5001e41d03225088a03000021074040c07444014034046042c400d0382055036101c0e112a005909400c4207500880380107010000611007008041410203c0c800848010102c0c601c445980b4640f0b0311009145510100c840803845540b00c2c140b040040d045030607230290100f00900043c0e258602c054100d44c0502c20f5200d400c004444001c00c0c541d04121060081c01c0d02e2094031807 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 394663066 1250 394661816 394661831
    0x60c0f020312010332070f0e15041a120715050a1b0203010b0310020304031b0b070c020301060911070b0c0a02060109090201120f0b09010b0405130905010608060c040801 74
    0x503030301c07032049600c40040500940e006000294107180d5481190000f50b24038000039122040d000388201049071500050380c4030603000c2000c2038801c51083c1c044e2550000681460408160700c1410241080350305109588800c611041c0c034812001081801c94014441141550450f90040d29284c15005004c40c10100704001c240050007941181c00190341a0394411590f1000c1301c4501409081c4841280e055403942da000d2160351b0208050401800c0a800050752070801d450b000d031100b1300529201d11401001807280000c24162484203034010f40e1420010354030a424400680100b007190003035040980b82c111603101c4014214050300c00b00c5c3c07042e0741180160307c9014180102c1c1c001c0e01c003030340d0041e40500c00501100600c0c0d0451100030b031045c103250169940984540b8180e03900040f81100e20f650ba1031092040c1d28142c0b43d07550040041c805d04616180c2810f000c40c4440c81211001940b4235140d1500c6010040309602c0540286003031420342d2194113000d030703c460301076009100c1d0711307401e6091403078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 394664316 1250 394663066 394663097
    0xc0b0715111b0f07170f0106031211120708130e01121415012705070807020c0a050114160f110306070807090501120e010c02160801112203050307060c 66
    0x21400f40d4000407100815802d03141c01006034201900c0c00081c442c500480f10305a40d071902c03d004210141d84504426141540c07200c400a2800744581800031140d848008000ea0384101c0100b01ea1086030080c0180c0d90fa0240300d60210002e407025805403418220500000525001011001030090700c034402171300f2100252704081e07035941a080310101c00540c01c080104030004008070704902e980b039a81e8000c0751002581c40000d045620881d440f4020500300410015070310350511609071001d10850302070ba902402c3c0800280b201e0b460000407420b001c0300007038045048080036900001345a2140c9002044040341c0b60052100b21074604c40c030f000340300d8900481c44850052700c0440c440d5445954a4896906d048011504d80040b001901200c070358645400401610a019200d8601820340041c568001d201924040b01902580151060791401208144030311030340046441261070480b8032503d40090100c50001940c0d903074002801484000390740020030400d500512881200c640390071992155520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 394665566 1250 394664316 394664323
    0x20c0312251e15020d0929010b03151906320a052502090c04081b03010608060a2a08130303151e050a030c0b0715111b 52
    0x24010042c146070500c0080c0802124403900e007003030240342441c00318a207041c0200c0480c0c1c003800803412070315180c0c5c0800c2c050001008242c0052107030304a80401600381e0003480d041c0c00301e06000301841220008082849144030203449030001320000d001c5201d6403c0e0740020380002c0e44610861011442c2c003404040310038110040e003400d1076076100200e1a10300d620000d8004940c0000203031028000c0a0180c0ca442d420003c0700b111030781341c01303d80b200c1884c000c600400c0900407000348410311400c0200000c3c06440404251865503403030b1300300104d004c0c017a0f810009015100d03a4000d80054800d01c4100040700901d5084480040407440c80c004510100702114520010810040c0700458038060205180c10200c58440c02240d0003403900081c1d00c51401000b4842703080b143c0c0105a070111110a58a40b0180d8103080c3c0001d05080320000e003640c0c0355680d10b612704030340c80c401d840d40404c0c080758a50074000700114040d03003002d00c2c0c0000c100f44e103040710244c04103402507580107110803488140b00a0035070000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 394666816 1250 394665566 394665637
    0x20c062202060403030c02040906050103050615030105060a0e1e1003150207081b010e07060203070b0901140615040503012306010c11040b0f04110a080906010b04090b01020c0312 78
    0xe0200b0785032a040d81c5080d206a54881c00032a0400d6072200d80a010076128130826001e14803507009040c03d400d040e20b51500070803c1004141c0b10b40d1520080c0f10041d0f480b4413800003100c0302c030f034201c0d0701c199102c50341305100c40b0b003020010103808219420440c240b042c5001c94005d803441036110700d07401035950050b1012405800c0c2c000380910410080029200890950304020002000000ca034a030300620001c0e0600c4060f41c0514090fa0001c034125081000801c20a54800d03103400c001c000074803c110440d214694040c043c18002e0b1040c2d0361032403112840a044402409002e802400481c0515180a0484a08280c12420148200007250385036106005440700190032000e00200750300540c0820000340070728104a07070700401c45102c0c103880e41c8860140402d48121600e00b40d807210600c000152510100400c440806d80003030700180002d182c0b0b00103071404d0301c1402e403000a134003244800507407030101c030f00c0300059040c45a24001b40c03c180b0107078024004060100455283d822401100305014001e9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 394668066 1250 394666816 394666819
    0x1501180621060612050c0c07080303010504111306050703050712080103120e0102121809011404051806150a120615171b06040b0c01090203120703021e030d020c062202 73
    0x1804da21180b90009802945d0802c416404152900f10201402840c19010358070002c2c4640010004014030301d011b00c01c008100b05403803201d03850415022072204031342e101e6010310030034408042241c10500d4400e205a0310502c2e40505600480150a070024090b540244402c480d2440090f00b607040c2c0b00d01c900c151041e40b0f107041e0018409440c00c00c24098035a00306054242c0000c2d010b0001c20381c80d90742e800b0414024004a8100f80d02c17824004240300944030010005112910b806c1c414480010001039000d80c00703115402d4680189441900080b06c80d902d952003145400ca880d103002007130000c070390310034080d520b2078180404100355102104040d142108011800701d03009141070b0240405080f0b0060003492009118524050b11030869044030b400100c0d1040c043da554440960450904101120002c3e1031050400e0814110340e400a55414070a8905100307194001006081248100b0642e045148144019919020001e25040e80d030a004c607182d00c8081d00794042a622003080003d0032110580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 394669316 1250 394668066 394668077
    0x15040221040212151e0103050a0305070503070b0108010b010807021f0e28060b01030b0904020f01020c06160201090b192706030609050f06030615011806210606 70
    0x412046030032800c00041080c0e070000d41d80c1c860444160300034051300f50b402070582c19810762410301010700d40c11503960a03d20b11800c3d1000c40148041500090b013000076960501e00709964100d00d00e07041d421401008070061000c100d40d4004a070a1034190031501404800f07030fa8140c111755640f1402c81c0d66207200300101281d81e5400c14800c02d00c0c09150801000e210f40c00040f1800c110042e1000300e00742c02420020402203184440d2002000614010303030320600002d207012b1080c40c219400050400310f01800c000e204999150040c01603074000e11410400d56001410291030b00b04420030801c0c01600c0410480c005003a1010100c0d00441100a40741008208a21008203841c40c40003681d00a0780046113032a013003c5a900e007000002c2c24001980a0000c942d80400c0503407400d0003000590350044c2c0030180311400f034420450070f500c0c006039841d40443c0b52002d21469154410040c0c1d041a48800c022030085142340000c14811780020722242003901d0300071150034003420f4074840c2045400c54041e800000d0f8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 394670566 1250 394669316 394669357
    0xf0c0509010c020a05031501060f1403072105042301020315060a0c0c08010c11060402032503021801030b091c0f050c010e160f0e240603070305150402 66
    0x1441500d00c240c00303d1001e801480095210000686843c4100c030105880d4011310700188900c6038400c0d1034031301003030032403e0051860a007144405240c1c003000f0020800c02078540d4036800710064140b40011200c034004801c00090801b814140110040c5044484100ca001c5041058103032051088a12903d10040d10365641000782040000e03d81c06402030804000352003e000c0301081546164100030441800001100c400310740001e08049d034081098446500004104400740c1ca021410401c0d0000c60b4403403650100101d000f000f00824180c201941001e40c024400c500d191542c11100d041e00c0c003c5988401b5551164151543e86d451142c0344440c507140f440445212074094244000321441c0e0341041c5080c841c02da80d0603800c4440c074800321340480e403068829045c0710102c0d03603500cc040c212440c41502c0d040c1c18050141e0501d007003e4480c01000c00207105041400c0c0702c50702c001d40c2c4100c008003440c0d541d04000b0f8005000c0c0106840c1c8200c0d8502e13408130070506c4c0c5481e04c00c03101c1d6003568501c0b1458a1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 394671816 1250 394670566 394670569
    0xc281404080a02090c070c0b030411040605130e01110c0c0310111801021e01021b03040605040611010b060c06040b0a1802010f021006120c0e010e0105130b220f0c0509 73
    0x40170300400c0b82c0749828484400015041080080504401007540d03880b440c180c2001c207150714403d21300301c0c092880c1060a006589035070310b003120f40e001b0180b00410401108000c041c01054001040d0b03003036040210303003200c0e6084040b40d014120441142280d100c42c03880d80d5078008031003c910120b1403c0700100301300da540f03400341c80c42c9207003074107050054921302c226407910400c501e21440409082c0341d600048080200040354041041964080c0096007400e0038580701420a106a024980900c0300003084001c0703e4000b50044890500042c1071142c4071030328055456603542d001d07a0100c40c00c2c045200060f02180d45446400f0303008072400c0e400c081d818515001500c401c0c00c101161800c6000c0c1ea000d5051000c2d860103003a0041c0300174800c400031384180781407040340000700d60440400f40d403102004105201000c410181580c034202c980801070305a02500400a08901e14440c0d0808410b100d8445059544607004100d22011360040c4404d075142015041220110b50404000c0755080c40042c0a5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 394673066 1250 394671816 394671829
    0x10b0a060c0c09060e010e0a090206180307120501291509010203120c04150512150d05060702070603180b0a050601170115030b011b03080c281404080a02 67
    0x1e80307010300324042600c2d4990110300c042e03450702e410185100d003025004100d8032070794214803503100401c0340d010030145009a00294040c407800354603410400841c030300c000030340d034003070101d0740007011001081090f115082c9080341c040d2103410300208414603504070040d1a1020100c014078410310051450f0340d40d01d140f001c9982c250300f10090442c1103120070f04c1184a03070300b031300540180182a003004050f213481c078061a05042910507512841081700600c1075101c0e0102062619410801d0020400080c03641d000209034281c0d030008001c0d080e403040805221040e90040740e0305049c1c40a9640034040c1107442d210704001d00c0241c0c1c4005090551000004441c0c2c032190b400b49800500c14506007000c881c090150b85143d030020780002d91004583e5420a81d02d40d014800d0001400c0c080c281989240071060801c494807500f01d101074240301e038500000300c20000a60494130903011a00708000c041c1c070b0002c00343e001c0440050594021404000148400303c14100c25201240d000e803000341800a000d60a2111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 394674316 1250 394673066 394673087
    0x10801030c09020f0f0a0c02040c0e090a0209030f1002040905100e0412020f01110d0506040e1b010507020604080115051207060518180f060609010f030207020a05040e03040e0108010b0a06 82
    0x141c00810310505400030b2000d00100646003170356441c080004964010403042b203046046540510200c42240c8045880b04d010b50350340701c01d40c1c400c0142c44082d4440803c2c108215500e060b903460280170480700d0503009035400703231041d03030100e000030002940c0e907100c2050008110301810345884813900000e40012400b04a08690500c0c51042d00e8080c1c4000b000c050940f1403d00101c04d4096003c10071400011280c0311b81c65008000700d070f003031002d2040b0114650310f611130541180141d88081c140d80400b81d00410864111681c0035010715581d6950701e003170f940204000481c00280444003400040d180c81c03e09018100646040c015148052410f00e0643e1242d2109200c03403103032404c401c034451082d600d00c080308083c2840912171607140d19212060003250840100024407540c824807000311181d0344040d14104403081410b0041c0d607104203000040300c80c00320f40c2c400c69100b400d29401c090940380c040064000c0b504c4401d07254440784d807038540740e50a8480c4c40340110341240300c540003005900e2160360141c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 394675566 1250 394674316 394674337
    0x70305060d260a090911031005010c05010207020603041406150625140606130e0d03050403051306020f01110702090714071e110102011419060801051302030705010801030c0902 77
    0x100804a410641d05034112180100201e00070381000c000180c254018200511b54651405243d850641441e4004403800d0240a0420552a60650400100f541107886182d00145590344a00c0d0a03c1d2200d140500030f401c00c800340c05540003140c0c01c0d480f03608032040c940c0300060440b8103140b2404003000a0f1440c5003031300000d0044110a02012840801c880e80c0300c40381c600e0207043c00d40380c0a81880300074440140e0a100d010301d0180f2400088401080000040b045482c000ca0551101c3c20100e440340903a002d000103511403010001140c63300028010303901440b2600030301080d000c40cbd0007540940100e400c003a4018141000080c0e402c1c0c03090041d811040701c1e801c8140d003040c14544138481c030ba42042801550509071030307101c0c0c000d011b0444021031031000c09100030301040b2400044418049000303080c1414801c0001204414144250004805844030f90020841880c0107071210b290350349104000e81c020300410001240e00d5200c1c0c0c0d4981c2c1602d8010380610708492401c840000258410315107035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 394676816 1250 394675566 394675613
    0x30b010203120f0a02210406180b0c0d0b04290d08040302041805030d0608070b0304050d110f010f061403010606080c030703060e070c02040609020316140408030406110105070305060d 80
    0xc502504440c6c2c030011006100045210300d0300e42450540b044031041100b420100d411145200c0010b607408510541c0284c02c0c0c045c0544981600c40c078080900500689583d0181c20f100610130030240041030a002100c10305196524841d48400f0b01080003440c11018200fa98204030a00141c189600074807400110f50b16001c2c03015040d92103d6043d6000070703058111080e194032040018038410070600000c1d01e0410145481d60030541c2c2d440c0e54032980f5000c80000d00640c2000c20403142000c0c0f042d80211034140000f03104003200080c01200501c418014568014240c005150383d03400d0512514042c0c1e00d4a071100c40c075584030b40300f0004051304020140c804054403500040368080320783c80e105003e40000e40310000d0040e5940b0401043d14a0754104064052050003003108210390000d01400010150820140f1060b1016008000340700741e4010340051b10000500154440d880903c81d02c0306070310f200003000b1a44460104900740c0c1c905840c2554000c40d0024684003180104599440300030700f01750784 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 394678066 1250 394676816 394676827
    0x212090604030c081606081014031501060e0310020a17130203071503050901050708010501050a17010618080105040309090f0e0114090f0c150a200a03030b010203120f0a02 75
    0x1440b0041990f5000180300380c120300d01c1840c000002c40e031201c01501c81420547c445160611280c1c1b84244035102c0e8803124045d1100342d00700d988082c05819000d400c85429a6225a103c0e0009011010185203141c024407a008200c598269140b0a503081031706240d45a200c074050b041400401010040e1080d01c5814000c42c03000016501000180020310702d003d00d240842c605448041d0841d41d00820081c803d03410b00080100c100e40c0b20b01c016065901c03d00300191074070001d20040380c92039100440d801e8900c014000110300650031501c00d101915000302c605902940323481942e130907120192001408209100703000d000c140c00d03d0b086002000d000101c000340c85080d0710440c5080d210034280b6440f8084100307050200c0e11801b1700086c04003040050081501c2480c40c0003007881810040048034281c80041401c1041d14800e0186403c03030b44128411400b000d1018000946030000350700c2c100c002ca441d000e08030b0441d50021041d1080d00701035241034401c40d60f94080b240e900000040c8043c0d035440d401c014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 394679316 1250 394678066 394678073
    0xb07050c03130f14060c0705061e0705062710090201050d18141b0609010e0a03050304063c090503010906092904080c0114070f0e10021209060403 64
    0xb0340042010703040306001d45103400c04100649441c1c4100c07500036031040180d00244800014098101d517001d03101d482d0303100090603450040644d0b1426001c0c00c0d403c0010810140100010b8150041d90301c0400015022000810091094154441b80050780c0100000000211441c2d20120a49006041c41131406179400700c2d4608440c0e06207941c050200c03848041038144915004202d200e00c03a110020100f2007103454403e01c0341065090b8140c41342034000b80c2000c1c40e9210300301c0c84041c40d001801e0201d150b0340306c0c82c107581c41c1e80241c000c030800203880c0e10301d00d0034038032081440b0100442c00340b86840b040d9214031401d007080d0003860090030500105c800b001900391002d1040841b03a50040760005840300301403a00c08200c00c2103028451a51a85583c0000d8071440d0340000c03604036921403c00750b92450381c1921030340540148403045417515485420010f500b5040b021700041c5035119607855903800c44201c10045290312045d080c0e00141e21880c802240003100d4801002ca2800081249081c01d95a54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 394680566 1250 394679316 394679347
    0x7120e2b020402030103080a0f030b06120c121905090304030309261c140c03030f25030e0607030e030405040f0e01020406050a0909050106080c070f0b090c10020a0b07050c03 76
    0x3403040701da407240041c0020380d0342d41c40800c20986102c146024000b84072f00c940060124000c58450264172000302001c24107591101049444900d00c001c220500c900c0c0610181c031034010f0f41e0f9100040241040009451620044101c4040d20b40c9515040c4003181014a948908841c0300b003d01c40340441034041c1c0c034120004029800c0d1000c02483d02074164841410014441e07100c040380100408404c0c8070091203903038040203680c2c0c05105440144042c7c0d659203240702c0050000c5a000d50422079903e220400da603419004031000910710011560f1984030448110100c64040c1440c01c025007003808207002516180e00500c81c0407804950200d086000c9940c1242241d00c55804400482d10009a401035140c1092070103009001d521000c105540c540303032018200c50001000750700e0649000408800308035580200c80115504030783c80c01d60b18030388003108070703500c42c450380901d40324200c040c2030110228400134680c070509500c80a08041070310707100425030307040e0054001071540340000d0189040200100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 394681816 1250 394680566 394680569
    0x2a090109050604090f060605030709020c030d0b03190c060905030615011214190c0807020a020d030302071b0e1302030a0b130228060306051e011b050307120e2b0204020301 75
    0x3000700003075036031030708c0300705860020942e01120f9424014000340d400c51030044141c0d0300444440401003028905040003a05004d18500e0340082d50b09101160014095810300b00c0040d03440546594212075260300c00c2551b10b440840d0038000d4880c42c03080884070381d48036461030940c0098000b800700b941d5101041074000e011049401c18142d1000450a12890641780280342103c0d1950a1881356800d050307100a440e1003a10704068010080c04000e0000c0503c40c0c3d04482582e50008400a14880450003110f1070004512601c1001d002c0031000c02c10700713041d50a0746c260301540180240f01c2c540c0959148003c8689c01459084c011200070709802c00350300c1c1c403a81c0700403900b02022480000b21010107101502e031010382000c010903140010030300c6141c4132000c6071000c002c00f000030000119204001202c0c1e0070364042d0f402600f075001012000c100500040601300091092007134a040700c546c081c080ba500444080340d6940612801d014203010b8401c07030606041e464040700320b51603043c160b80204040c0c5c0e20a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 394683066 1250 394681816 394681823
    0x902281e02010e060609090a0b060a0b0318010b010206131b211a010f0303080a2009030105010902030403090b0f0c0d0503040308060910140a080109052a090109050604090f 75
    0x40f41511a081e0348240300d002d5100208880e80081810300c0c00482e0795440304030100400d001d0049020410b59611004440b004000142d000d99070f91a1401241e0264203001d502810f0540c01c281c6144060344c004107039103103d0003d61004004544140c2c03a01003a5448100c20888a8107104034086862403000d40f401703144200e4103500c040088881d203041d10001d000d0180c81c42c4101203605c0188401488450b0030700481ea00351604100c15190358070480020032003101e0404040d4441c2680501030004080648881071048000f04856a0b991040009038413044030001c0008020a40038808942c6c2000600219000803441504009840c444180391014150700500450380c04000c100070158000d00050b0b00401c15500da852034202500550321500d198090246e160014850b824555140c285089000b040380704024003849845082c81620389481600c0640003541484100040d0040310490010050000e4840d500aa1030f00f000c20009003005407841e0b50003922a10b420010540146458640601 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 394684316 1250 394683066 394683071
    0x1d0a0b090f04150f050109080105071e020f06040308010618050f0d03111911010201140423120307020f06040302031e0409050405010b040605041802150c0a030302090306010902281e0201 81
    0x1000300150807c001e40d03100c0e22940e81007038100071405a022212803481d03001e02d540c07210410440c100a034140501c618511840707100d0402004141548019071a04898158503001c80001c078a040144140026000b401d800c501c001c004c180030390400840c49242d413070291a140d028403446a0800d41031029004402c10706010302c4c6076010600c0b03440d0001c4500c0c070209000030004010b4a01000e1501c02d030090002c0d10810340107100344000140c11015025a050711030948111501000d6141200c0c0c0050300e0000040c880e04040008a910004407180903d8050b00290b043c4100703a034021515000c008503250f1828014440050110741768003c26018130300c50000410300340303c958140301c21a4050303440280f1071802c00c030740740c2168296000d81402d00d64040d0303500100ca82e09010034a401c1c1c407a1901c4d8211034401c01035080c0c24998143d000d0400103000310160b8110380d0740c40d0b9404040c0d0068045610300b9101a05940100307208414900c00c070014503003043c0c0c40c8034046201580d80b4a44000100c00540d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 394685566 1250 394684316 394684319
    0x3020708120609130308013503090f060a0806040b0f0a1e0801140f100b030702011e1806020c0102090603180c10120c1107080c031002040f05010804031e1d0a0b090f04150f 75
    0x2f62021101808a4060300da80d418001101c90081000c2d00140860f40545c1d5580410495919024101080c505024000ba000344c0e944000c80801c0c0300d00b0354188035142041c0340d404a02800180190403680c1c0c9401c0c0d0035600c58840d2602586200c00150055000b02944040050313a01403181c084e41c032400c83c6d80c0000411010101100d1415843c0c804c0300b4444901d03190b59000b82081980c07204071460303000040180c5400ca007422890083c413503a0b9425034081d40110801010394205000d0400300d014070b0307058030194141407041c026180d1000d119900468808805c2d03516000d0030358030644425003079207861020503065070300c5103040c8034050308648c1060f0040008039601d418200a054410040504110b191030301d4417540b444005010301465040003400c3d40400c05040c41100314012101d401d04800d004c09606e41c8000c0c041241d50810129030807400f03030040d2203c0c54807150000807207600c42134880c5071190507410000e04252502d07081e50310503515500850490330180c1c11401908580324980b0380107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 394686816 1250 394685566 394685569
    0xe01031e2405070e03030d0b03030c060a0e070905070f03090230150103020f041e050c09090601022b12020d020c0606030703030905040c0302070812060913030801350309 74
    0x114402081c400030f0110300ea01c510740c05c1c2c070000200c0d066009184c200095003e100310000341903210b1a00c0e0400c3ca84900414001010003c5c0d00858101e1040000c442c440c1d5510041031040d20021107047c0041804070310002403041c040c2d0020808544024410714640c3c070b0800350b0203070360000d09201804080c18a48a14556402003091054000e129000742e141c543c555800070312000e84540b905409582c03904030b000540310407a03180340c1050b4084c0da8140110b280480050341c80da00012000c500c10480d041c00705881d540003084000404d491000301c09400c403280000214070a818060200030051454040110800c1d0751002d003118401074080580d891481091b01f82c1b9104001c1c0c20316200307030080c010400010b07400c1030001c0204d0f5402c1d03c0100ea04080b08078244c00074054003101600c200e40015490004a9131f80d0200c522504080740d1032515138030340001202403481800c40042c041611140144242d8500c100341d18600d0040321282200c001d41c05410501c0066007080b030401c03590000c00c0d5a400d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 394688066 1250 394686816 394686821
    0x60f0708060406210813060203090f012109150c080907060e060a03050a020d18020a06110a080d15170606030a11011206050619080a0203010e01031e24 66
    0xc2103500b80125420306540c001504d58040c07000d15480c2c008604501000341500654010f418032800302d40b1101d41e210700194481d8001500c03144a0183c0d441810f0701c560042242d0382c0c507035100b440e2000c0c01440c400240c01c01400180c000380d42c640c0c3c40c0e0080245007041c134060076550208665620415081c0020300d9440d0080d1600000e050041c402200a490745544040d6003086403940b9000c03407540c40c0c0d440902c3c028071a0071302c51005142013040c90704099480b02103007022240b01781e84189170f0341e41e100030485150030600c0303000c0da15401507020840802c020002802d1007441804d800a035000140d40e48420180031540719800e004410302d1300700100303503080c0100d95003c44190042c10108906944200d04041007040c02814004a100080780558081c5e000802815000e403003265110310507040c40e11102c0c41d130350483d00068079613000101c100c01c1c0c60090703a040340d19092007009070341d09598070f031140032070040c24191070700850516410210700007845803007003c0c007541e031800003403c0d248905009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 394689316 1250 394688066 394688071
    0xc050f01020313020d1103060f0106020f06010803040b0c010b0d061b11030318030d0c2705090705070f0b070c12030504020907050c2109030d0c08030613090203060f0708 74
    0x141039105100b08199050b0f44040d00ca040c65049800b00a1440685800300503045290031464043c8a003004001c0a04001b081c0c40703060320030503002c4a51056060483c556124000d008501d2160411301c400c0202032000000361249505210010900074031140104035000d03c1032009a0f6003a884040380e035528002c403208408001c4241c42e20203513904001200c56030324440644400f4070710881c0d0619003e2044248140d0301d0f2124010070a015450b046040140300260010704828000b42c8448000c0000a0034000c60b01156000342003070149a540100aa4180d007004409640c0c004004c3c506500107070b02d00030040d2180b410303920b90200070013013800c0110f01060507105420a05281c074050201694503030703080551280043c684036aa80300385000407802c210a41c8040b402d284800000c0c1008030181c1000381001c400103070308880d0401e281842c112154102c16502800e441010408510242003402000100c00742d48100410641d071076502180c507101d01182c001d9250b00c1460180318125a20015194 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 394690566 1250 394689316 394689343
    0xe030111040911122202030105090a0302010617060a0c020102070503070b04110105030f13211716090e04060b09040602130e19052706090f1203010302120106080d0c05 73
    0x2401c02220b03031440e0080c0000070300110b00c0081002080c0d0840c038059601c440e007086c1c1c00350081c0040d041101440c0d1707550000e0b5008030099420041c0104be00461441d8070510381c08524000e1010b0748495540000404203400e0741c0c42155020811213010410800c028140c0780c0c881d608545061802b1f084c4086d100800140c224100a0304100f8800740050000005170800d00074001d050004941e86090350340c0010184040d003942540501d9100700c9900424420072200e11035583c00d566613210700741c0014485007402d4000118101c50702c00d20a0342c00002c0b803103500500c41c4600107411600c1e10000f0b81410340171076003210bc4580000c8c08031510106002454001d2907482949500390130581c40101c010960f92402540d0f007691900040e84aa841c101c41400c80d0f1115075846501d150075142060b1121800c07255260584a0b600b440c04141c900013801c090142c070066007040c113507400c5a0800404050604086095649890300800c5c282400c0c48103101500c0d240d1602d07015000c6c00d20740075080ca801c11320241e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 394691816 1250 394690566 394690601
    0x3050108010603200a030b0109150e0c030f0c0403080d0e010c02070303270f0b0910020a030e010e0103020d140a0c0201021314130501081b0909070e070e0301110409 72
    0x10000901d0312213900e81140821884015600f0281001c500401403a82c0f01403c030820000c00000c50200380d5120341240c190312120b03030f403900703464020644050b00241c4041001841c01c00010b54a189044d07022500809411080d0740352581d04d1b114403061b500805c50340e8174160364400030340c050900c1c00d100b0b013440c0c030025002902c2510300d5528040d1001500440b03058610300c80d05a00c01d5a0018003280302c01a1a0381d5a1490119440b4900d0310015004954101e001d802c04441205c4028000102c0100340d5a1550710310064401c030700011a000f407560354035241072503024000c501900503940100c00d0351902d201d10711055898410311240903248490f03041001c0d644100006056090203509a5041d00c91a2400c1e1a0700768581001c00c11009902a051300490f28010021942000104d41c80901d203006a11841c0c1d50080c00040003000d0f5001d4611841561200c0002c0107024900c0341e180780d2001c21801e203082d0b901000e00c0441e0a49107a018034059900001809100e000c4061003407070340c2c40c00c6c5507082 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 394693066 1250 394691816 394691819
    0xb04050f04020d0b0601020c06040305010b01030b060408030a030207150e0d0e060f04050d0507030c090209010e0609030c1201021909030c170613081c02090f100e0607110a030b0106030501080106 85
    0x300f03614415030440a8000750302a4000f806a9000f00146070326190040c0c506503907240e030f07401c005000b480710940050000707082000c066030340e1070404140c0c2d05450041c0c0c00740d0b1500100c804140e00940c005402114041e202054549080041d03115680740111700704080d103101c01e10840000c00303021848031128881d0005001140c2150704030300554059550507a06486d028105c4c0c18890f180046550006106440d041c1c0085460b030703025000303010701403020380301c19001078000010032100740100d1040903056400324025002320701d00414000340c0c40f892040010700c1c0500029904d0800c1102c042d0050200d0701400d0100104850702c0b44002c000c2460b044e01c1340d191201c4002c0952540d03006041e5624070508030310100103200c4564103c6200b1403200c0d400f44c20000000a18030040e4001b9084030b44100200c0041c48414200252041e0340010181d4403031080740e040304100000c54005001c00c2d280c81c880a02008403584920302404080d5000d14844500c07985420801800c0e83e2050b0040c10301d0380d050100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 394694316 1250 394693066 394693069
    0x50109020a0504030f02060f071a0a1404060c090807080c031e1e0f101b08090d110703060c11070807030f020d0302030909100515071e081603030b04050f0402 69
    0x5907415039501031740303240e103201c12400000d2490182e603031083c0050340c0004418041260b08406451400c0383d8410111040d03903052170340c13012034101c41150540c2c10f000c000050300007004d907405a11000964241445540e4840c1615440d04980380c1012409510611902c0f40d61314041240103590310000700f8070b200b0003d01b207608603120a04610992200c1e940844500341140044c044480c81c803240000725070300c03840c1085c60900942070941060303410b5030541940007480351003403482c81e00c0341c0d010800822a036082420200c6882820032000e0f4124000c070000400000c4c03140c065510071842982d40d54a13580c0c9811b50540c14030303800340d0000c040c07035001010800c00140700403201001960122000c0941c0da140e42026411485000c800660001d4200f0070401e408035030603109000d171001a07400d1601c000c802000300809100c0e07407102511580010840034404d03070aa4043c02e4546e403044030414100412510245c0242080000c2140842e03152020110507050900c125944443e03c0a15517031181050740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 394695566 1250 394694316 394694327
    0x10c18171002032203090e01060201090507171009051005060910150507140601032a1203050408191a0412030c02010e07080a11040e03040b0901020106031a0901050109020a 75
    0x2004076811030303000300000d107280b8a003180e54016609125901c04d2020410700d401000d4015a009003005001c40c1e200101d0340a205101d0207a01d075901c0303001003410500b0001040c048020810a1104520405000c082410b100780141640703a88103000400000c405c10264500340c84006042e9070003000d00c1410003030350b580c840e580941124000c3c1500000320083c120704441c207114681c80500440c814940b91302c000c44000505a040b00d00403491150340e1a03510070407a0b445011441c4002080d03610300f10502c40c2440d05004800c07070601c241005483c256481c0501c03030401000c0c0c00303031080c4801c100144805001e90002c10f5561041c2c0b4000e1104640b0b00755807209045010095100e081680e520b07602c010302c0e8004d5202003031886100d41250441e5595040d130719030f1565050004c44201c00d045066038020f0405005001c0c1441d205000366041c13600b49101750001c2c1c3c0109410a0440d9201c0000001040c1c824010602c41080720000910525001043c035081d81d9040e40110344142c410896050381d580d000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 394696816 1250 394695566 394695583
    0xb01080601050d02090c030421050705010e010b0117090f010c050403050f2d070509131407050607020d06020d0609090201080601020a23010e0f010209010f080112080a02010e010c1817 80
    0xb00c1c50760744940710703070400d030030188150203280c40300814105609141540100160142f24400c2c00203000303960f0304500950a131040d05415601080d5009454010500c0a003100750b80007140904030745688051282d041d003510041c3c9035540100310001000c2c400c0c00000d0116035155083c1c5802415021209841b20b1a40001d15040c1c00f501072a1002d0141d0206044c055800207020003030001c00c00741010f002c0c104513804134040450310040100075411403907030f020a801d000c441d0010070b800d0800d19540c00384491006401d008881c0c49034204128243c0b12000c2c07040102030581000005865655440007502900300680303e54159484000c0102c00100144010303050364880c5481d00c2c0307129031140c002c9030240101e01d1074110140200c280e000b00704034055018181000b8266a800b1134140394110540e0411001c0c0038072074a4600403150240030a040600600b051845031000040010040000608640c00606c0000005548a10082150b408000008041c040b401e0000644120030b460440e51610075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 394698066 1250 394696816 394696831
    0xf02030f0f0706020c2a0307050901030b1008060c0307030606020319110705150903060c121303110d02061503010e100b1c061401090504020f0405090f07030b01080601050d0209 77
    0x61960403c0f407181c040d240290051421240003007114403034034054203030015006907018000300d03110302186800118842142d01c083d0091155034215225480b2200d0014004810780320504030020350300c901007003d14072500c44019001d860b41400d60300141601c0042c3e12110841d0300500c1101d071100001002000805290f081500f4041101100c05061101980c0410350040810550342003d400d25402000201400c4064440c15a1035012108050080d05103c280c0c3c0c0030104d00040107a00200e002c2441d881c043e04141c9040b6070003a10f03481c9010010015440140c11107828088124440040b004000c0b400b107000380260011280b1042d581c42d280003240c100b81d80c072071410034103540303907400c440c04640c03440c641c3c800c80010b10b402c3c000054500c001d000d0742d000040384000504880c0610400e4000c030b03401448003050300064070400c006080054003407425400b030319450300c10308a070401458009601c41d807040e1940c1d601d406511801c2c041c059110354000e5144000c4d48006036502807005502184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 394699316 1250 394698066 394698097
    0x80a0c02090703062d0f0905010f050402030c1b070f080d030c020732060705030703020c010e0109050904150203100602120408060f0919080702091005060d0c0315150f02030f 76
    0x17080071103042d0071009540150301d64494a000840d14500c42c0d0031043c16180b900f035805480e955103c09000c03c03484122010020954107000c1405c0410f50000c0041e05d22100703000b2101c0007500c1f482d5141000d9942e44c0210241e900c080e81099559402d80101d191080c098001b46c50043d181c04552600c00401030b0120410413983c154040316130401c00c0508a4850018081c10344401180c640107a40303600c80c20054000d881140e0708095290701c544500c001c0d5410603942e0044175071418040c48801c3c54050b001b01c440c030485006401d1901d0240c8069446070a625400010b0302d4074120029040151070483d04520b0b520402060000c840c000400c20f40143c2055a022640c0c0d07034069419041140a0782c0b2100c070282001c2d0060184103525029020311402110091801d480d0031060040e004601d01c541508100103000c004e4042000e54056421b000c0c141c100419903d820040710000c21015410042c90f149241500d0174206902c014180101c0856000541c50200300d85001e00390360150041c4481c03181d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 394700566 1250 394699316 394699379
    0x50c09010f1101050f09070b1608090d02030a03030218030109080a08180d090f06020d0210110912030403061d060a0b0d0b09071509061707030207080a0c0209070306 72
    0x240b10303500070555000358400070061030070504040d508145066907081080c2c81118404a208085d200444400c110000440c5a00d403104c0d9440c0041500000400c41c3e00c00c51000300200540c8042c44803887d054800e81d00143d48200020340e100c051007002480d54000c1c0e1412030701c1000242c014049403c269031a081c004a00e44d40c000400b050000c0b0340301504500e00850012002c40c2d42c05c10900c0054440c19401134144688030607080b60740700204040310005920100c4201d08a8100754003082548100c203c6007440c140d44640403c016010140c01d000e83c070b510004042041c0001d52080d44d070001500380b068480b0358101d80a440d521038000d8070300079100e50390329200400c654a0084500446920418225141c030388002407a403210402d1081c0c100b0500650040c40c0458891442c10302135507010349910700e86c2d0410080c12403039034500800100c189035003000703254003281400c0050411030203150340b01144016684148000d5020190243c410f26003020000d010446000404003442d4014035003140020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 394701816 1250 394700566 394700597
    0x30c0b040c1d0709090e0d181e0e060604050a150e0904080705071e1406070212030403050111160b2701060807050d120503131e03030f050c0901 63
    0x210503588003510402d842225180c0300400c005525100d4000350311104801070b1794409840c160b440402c001035485d0482c5210a203d02d0145500c0c1e440d600c0c0c008008951240c8652011090240324020405500e848043c00c00a0301041560703150b1180d41030300c880742400d01d4500030408484090085919840f0801503450742c80348a114143c1515100070068269170405003441e6081d03a02104059500d8042c030b503408a40300c0c91103400d034000300f20f9020700c00040320700d044940880c0608601840d98004070070000c08001d81e5804c009880040c6040001e16541e600e180b03001d41c00c4845803064040c0900050220140311044141c07420112078011005050765a00e80410440c01550315607081a01310314000e4210034002c0540c011026a45010111880180c9034420040e428000c404001c0241c0a181201c1c40300c184910080e50f005149c249103003181da921a6030745090321700c08a5214106107104815507060503498020310011124000c4200b29906101c0d2140109101d03004015042c04101d0301681400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 394703066 1250 394701816 394701833
    0x6082d0303070e1003050c1603021e070816060909020306010512282a020f0a030203091512061c1a01031101020706270b1c06080307030c0b04 62
    0x92918040d41d5481c0342155000c0c244259050781c5500a0041e02d9000900e64040c1c80350a020311081c12040b410101d003100780c03001c6202c642d5012030450040d040400d14450769000c890000030781c0c0da00500110303400c1c442c020345800300d00c80c2070882c1078004a404004840d001410101924410140540c0c1d0755a2070300140c0c0c40f07118156401c03298080038000c0150355040c605404515149200141100d16110000c06041d00e03560300b02d10b601c1135250140820b982d504500e001c2c8000903103005582081c000030200d1418426001070503030244c0c20015041c3c0c0c0a103012800580202c041c800302e5070030700c01d000c8403c545800b40242680d004034141c080d42d1003000c460440d8100007036803021000061201003100001410820312007181c2c11401c01786546455800400c044059034002e588006140c04140f1030a0f1042084100c20400c01000300008110341010710024141c00203002192044100304c84a00c008543d00c650081c82650028002d04c2c00082d8800c030660301c02c64004001906903190303400c00200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 394704316 1250 394703066 394703143
    0x3031505030a03030f0b060702060d0b040e0d030c0807080f0a0f0e030f1c06031205030408070804140a05150a051c0e0a1a0c042c01080c03010f0608 65
    0x52500c0703080724201c10513a01d40c00521a01402d0380d0140440f0113030000380550ba01a13064000e50003081030180d0100c0104643c042d00000c00020004103001403600e010702d00301002c101594001035151f22a8030101a001200650400201c1ca0040080d1900409690441c032000d00b601e10308940710b210582c0c54021070f8101c810071451030384c1569940d841403401140d06510071035801c040b5800000c445250000d0741e1054104507504149000b120031050301080701d0740d500003402107030000d10501c0682c0100304036502038009088400f8124a034001c3c0c50040104200ca290710091040000050300a1207441c0001961014007043c1041034454124050b99044081001c00c0502c00d10314007640e00703800d2300700041e000c80c8a50140203885101c42c48003680d8507041008881031542a94100803c104804064000c000061040522104a06000e04140d1804c2500303a203c081d107035000c031031610982d1a00b88556030035468003007800c00c1000d1804402d075889150300c20010302012006587c2102a01c0d1540138440b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 394705566 1250 394704316 394704319
    0x6040b0a182103120e0d121503060b040b0907090504090201090308031e01090207030e0d0201052701020d020f06070c030c05071511150c0d090510050402090f0f0403031505 75
    0x1000035051081c50002c0d1000708802c0d000200042140943d1031094811529003400440203810390040b52a41a40e0040e1108001b11a1075640c00c020040b041009480c2c9000c2c5101d0715000c41e0401e402c604010030b50b105a12524414120002840070190b00109103100303c0d10192004510003c0c1c500050711002880c0e400074086000010402c062810a038011000c44180d0369801c6c50700da602e03201d0034000c038003440b200140030800d401a40d004501d00791050100003841490400c1c504030513088800110312414000f22812090450f500c095036030148030083e00c540140c0f005281c0b040d01204225502c0a000c1d04240500869690040500d4460f00052100e1034001003100c5000e5980c0840a89140070180301c100010b158850020701080041a1200351410000143d041381c2c0325120b450354a43c0c00044400302c0942d80d803802d40300140d0144507105090400380c07000030b26032034640148550764500030804031b9084814010400c0c16012401c4040d00305806160014072040601410080e00d0102d41042c4d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 394706816 1250 394705566 394705589
    0x427080406030c021204180906090c051e06091e0303070308060a0e0708070311041203081b04030506160201061a0c120a1407020a05090f0a0b06040b0a18 67
    0x100501411500420440300d46582c20000c901480c02e04985400d441c0d0700585500504010400854203000d04805100110040c0040e0308001e07684d4243c121420001c013181c156141c44410042031501880004d41c05001f8100c4001e800400c0d800181d10703100304418140303c0d080d81c219000d100006644144102c50019044a035103c0301d504018040301c10403607a252160f03042c407d000c14141e00e10340d01c1c40d01590b507540f620b071072a803284a0158041c1440071803d240200c0b052100042061840d01d00b03281c000e0203919450020b05058280c1054074402601d0340d108440304000420000d080041c1955000f0a440e09501d48903610507412805803401e54840c2d0700343d0b100d00c041c0324642c20f080c500400d42e100228040325141d010905004d001c50040c0642000410390041500301c42c11603403002012054030061800c2155a140c00001d0140d02003960307000d903c20749440812528a0302803164403411311040316207a01705483d010031a0143c1c8111410b00f001c0114440b16000d900041c104c1c0300000e4840b03020003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 394708066 1250 394706816 394706891
    0x30809030f03040f0c0b090901060305070e030303010f05092518050604090b01030c0206040506060f01120c03060503240106120e0f0610060809070314030c06010801140705130504 78
    0x138182c1d0900d180c240c400340700840c000107242d4103e8044422480300946120000d80c40c060f01900240702c02440007051100b440f0000e980c030340d0180b00440c0070b40b00070351446a1590400c0180205408006d0038151038060711418200315800380852441c54114031b140000020401c6c150440314541154440e5030003200c081000b00d03645815400040400f1401e03039040081c1c0d140b183c0c4c00c903958401502c002d4070b250008001b0404500380940c01049414060400501001090320301e00121414020b0607000a95690002e100c64a0284142d160200c2e08031345a4551f00c02402d001d141001c0c041c4a000e040c400031404602c802405904000c031511a0b10f03055803410540c00d01c2094484400310f500d1202186050700c04244e15014a6120f03020b603070b154006140141c110385d03aa0b0070b007400003400c808040c0b10038003101045c46020407545000c1c20030140081100842500c3d01f0400807070140c04441801000d0045501c0d04581e100c040b022203204907004a038268042040045200000c4d800d01011018942c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 394709316 1250 394708066 394708073
    0x41401200c041103100e130c0f0f060903051005130b190b04060303050306061612050c060f01060507110402160b010503100908030403080912071a0606030106050403030809030f0304 79
    0x1d281000550a4034180401e00c03007103c0980e4148002c07104001074040b2040c0030700c8140320307a02040d84e0000c4505034100c210512030710b401d02c2c1e034000360340305526244100c0b07814450b020f900c103209001010035003828280a42595034554903003031030800e664881a62000003a200a0621140c0502c807a04040240344c1d6082c44c00700e0300d42c030380301d2980c04401031800c1515942c0a81064031920040b643c256a4170f9065480e000b04100866102402202510b80400074210101c1d0b107202608081202580390b0303540e220361002c69142004001408030074001049130040040d15002000c446c3c2c0340342e000f880c08040307032a1000024003c3c003a01d40290407880b0700e041d6203410001340d411800c0c1a01c17001c50440b4001000301600505840368a01c0080c80b5031018004030700041d019461464100400e0b4096a031464115207207402c070758000300c0c426200c0a100c07076501000b030301e81150710b160411015200d59186605201020340140704512000301080740390b100185e12014280140c42203000184c0704280e40781040e04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 394710566 1250 394709316 394709323
    0x3060509030d0c27050a0b0904060515040603150f03080a03110a020a141b0d080405030a03032703020706051b0303250806011e0c0203060c03090c031204140120 70
    0x105518046000c44c2e03082c4101440304c1c0c05803012598000c282080d07490616660a001c0e0300701d40d03846500141c6642e00420203542d1403004100008818101d9a121031810100800f59103803214240064258002c05020225881c1a1241981c1d00041da00d50b86d1a02d071001280241405240714401c10703070105503601183e50200d004510540205250140c00503500e140341c1e15806050010405c44004062070a00c4d400c240b11104041402110690f040c00c2d0b607400400d0403d4800c410440000e5510032928600c12001007400a0800c2d0888030f0313002d400c2c00c80c0e4010795900c0c0c4a005000521102180104503084101d002d40d014811580c1520340700c1c1401c5034a02850040e4001707540e095407020700000c40030342c452210144107810581d100c012401059001c40c0d01c009400042204020034840d9010141c3c4007001042d000356034603580305580b4076100308038904060400da03200d40f0035007100d40c031400407900050540341512076001c0003c24445040d4010b0360b0090002140c0b44502190b8428100300322000f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 394711816 1250 394710566 394710587
    0x80c03070b090f0c0a0f1401260103020405090f0c13020d060b03010302030106081209100908031c06061b12020f0601230d08070311031c020408150702030403060509030d0c 75
    0x1042201c0440207001c4c100007a1481c00d000c0c0601c000d035802e004100202c101e440714980d00c00181444016111218145182c1e41c0350164040801c403c2c00c00100214101446101e03408602c00b030140c80e20011040719161501e0540360705a1080001641d8509003414a6044860f1075048440030000541ea454180825400911080e8829441d140c0005554500403d5080c45c0d10000400146003008a1081040c420322408141c000c00c2711504d00403d011200b08014131700f450b00c100e10000312166201014058541d82d40000b001c005401500c100c2444500380c1c030503c010380c00070307540c5120240c800c022454509040384040319445170200004031740f6009000300d0025990703c2c502d4040301d000c46040c03090300e049004d40100045001c2200c0300100b841004a486913031400405e503031070401c461002080000c00c1600030705a0f0f60380020308002250b0304008098203a603a650b880b00852400580103034070380c002e81c44007400c00d6444600103600a0f8050044441c58201440c0030842c04a07584001042c14a80c17 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 394713066 1250 394711816 394711843
    0x4060f0e09060f100b0715020f090406050402090609010c0503070506070f0e18070c062004050108090c151803060c040603050f250201020d020c0d0906030e0604080c03070b09 76
    0x10301001c074015180941d100f520400b1825000d0a0180c58150106815032001c1c0d001c0d20021002000410704140700d0000346120b030000143c09480d4141102000202d030b01300d0784118450f0344104240c10745902c0700e0043d00c40b244424240707035090a85074100141503100d02c60004001d03002e81320070060000e8000d000740d0815203a070383d1411b41c00700002d414414429142420020040c0f420070009040710311074240800b1491091002040007640b0002c070f00c908407486401302401e00c02c041003d10055901201542d4041d0141004000b00390918011601c04003040c0751180e13020100041119440c07040d4100e240e07101c480503085403458502412000714a0b007040c09480c0009041c030380403407040d03030a01030300038001d400c40032084e44c5162843e0304c0181102880c0c40e038002595000e11504881e0710842c80506003003d11480a41540d00c4c2c00d400042464105801c00030604d40f80c501c04401000e0f000566541c065801100d2a0340c801800c1d20039440c50003008402801008942c1c10895890000716080b08150340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 394714316 1250 394713066 394713073
    0x90201020a060c030207150c0c12121a030d050306060304060b0a1a0d050606071505060d0c1716060903110a030615051e030a12180303030519090f020f04060f0e09 71
    0x5007403002e4003038603108e250100000d8200d01c01e003030114000b03030000d040e0401c181c200740e40c0361004441d1020982d0400d0b2070103031a1208000b840105400c003485800c84014540c03130b0541c0b551404400142030b5010141c00500040d0759401c40c0a800c1d12038a80e0540a440720041406101d0300c5440c88080c1944804a2101140c1c201030104807039040c018280c0e0140ea80c00416580a41c05009a43d0b00402000303040b580d2003100d803407881004c11f00501124001c0c5c040a690115160a0058038031301c2d0490140c034048100358104020010161f20218110640e94041642d00103030200c00d00040000c0c60680000d05060710709088804c800e20311027000310441d24183e803440751203500745a04140d910701c03810f45940c250700f00030250000030b088154a0180309055003808e40a40c00821000a08941107400440c0442d5640c03060101034601d4200d481e0041e85e4005050108401d50341e203a492030294040001d0013003000440b1217440f0342d500e4000c5000703484c03140d00489029a5500f68552041c5082d51200110700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 394715566 1250 394714316 394714343
    0x2101030309090912030f06050a030501091218030f050c2e030203241c0c06020606031c0513090e01020a080f04022b0c03061d071503090201020a060c030207 68
    0x1203000d00f080b9150414480644a011040240c0c0034001904052a075684e4811020600b42d49501c241d03405140503000003c0c0b812000d280800c13041e00c058040000f80000c0d0340041c0301045c10301c0001015285d2001420b0b901d0102440c206140c00d1b92231125580c03060312031300300d2161911180603504400c400240c400c2654410030740d042d001c82c403068800e5076464179041807401e04501020541107050402401915403440102c50307580400681c0b030360484d036420400104100107941042480e40280d003c80c06403049000b0f80002120918241106d002440408144080c00c00300c4000c10100506010105001e100001d80089001750f120030200c5010415020100705007000c65100c0354800e69000e008100d01c0d581d1060f4440380201100c030032031500300c510072941000820940f448001980b19040104500e01d1254440c01102501030107032060381d020030410000420b8054000a181c4814103001030a0459800100d0401c00c4100700034125078103103010520b00310b41c158020140e140c0115140050030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 394716816 1250 394715566 394715579
    0x11030613060e0c07020a0f171005070c02090402010e1305073002071b03050d0906030902090601030e030708070b0105090702030a02060a330303020c03010902030619022101030309 78
    0x440c540c0c050281c4a00302c00000880c048030510040080c5400207180b80340a40c2c0c0e4503d42c000382902600880044080c4041c0000c6005c0c0c10000c090001d40484800e21080c68402c13001800b0300030200000c0c3c49107146001140942e4010203101510032000b40c20444d556010b03071940406448113a58100010f80324014013440c004000d80114143e4014802c40000f80d0711854a14010350800001030751442222105580c01a240e1071400008612450142c50110368200300649074004583c0900281810500c1080c01a5191190300307a02503000d0070005440c8980c002460b28600031114000c0c002000041c4030028070041580c0507049820444510791560ba901200701d8490107030345035090259000e000450302d01c02940e040724035001340d40602c4070324041c03004052940c901c2140380f4010242c140300d0424002d040e4140600d4880c15800d50080c840c40105a00ac0380d50b80e01c00800c8244030304041460b103500150a6012500f01d0750712191055201c40c1d02182050045000707220880100300c2c404000143c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 394718066 1250 394716816 394716821
    0x1081506060f121f03020d06020d06050a080106050a05010503011d0721050a0e03040b0a1416080d1505030705150c0109051e0d0801090207021201020c01020d360305040911030613 78
    0x179264082c082c080c007004981e680f64065001012044040c0f91117a60201740f94603107154800081c02c0e0800003003101307450036042c00b901c0b0609401442c108a03040006000201010050b5100120380801506c1103a440c00411030301030190798690b83c0c0da400c00c0702c0c206850002c1e80d046940103c580381d500304114082d6008456030b9202d50300c6200c42000c8144105140d150007000088140082a012145020303907402c1b10381c030390785091682101c00100c00700c2c2202c801c07030003441500c0e40d1600c1481414012400c08001075641c00b04c1d44278141c421511203158a11144a03c0140c4085641c210005e10101e8007520b880c1c2d4403040c4182c03540799009401c0c3c86503461804001012100a0381d2070f2611640f40c0d00742440e2801a51200c0003ea800c402503286503890034400b4401850001e1003400010f0700c91803207255040594840c00d503450300c240c0e840c070034800b1079549002d55001c840c2c0710080800c400340d129203020303101401070381c0c84100e02600d4000c9101d000018240214443d00c0126000c949029201525904 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 394719316 1250 394718066 394718069
    0x609170714090a0902030d0908060f010506040b0a1803060b0312030709031e0c08060901110c0c0105070c09020d050712020309150604110f04050a0e01081506060f121f 73
    0x5071042031128281c06400d15404068201d8001e41011440729040d0300460f140508511a44000440c1c40b5400c10071000140000f81e004403180c081c690495150500240160003030707028100441c18000b070600304180c0500c2034105104000c1d008484916901d0811200420b00340b0351b11402400303110480e40aa03c04030081b24403580490703c81c030071842c1c25078451401095205102d0001b03070102c51490400709080941c01d07070003806550000d040c90710f0400001400c0d154441c1e10740a00d00802e0103c85280040440c1c5c0d034030f00a90a2038080d4403020b0a05041d20203800c0d603800018010320026801c195512141c0256114600985030990120800788881c8120b1208491142141c3c014260a62b031211403003c03020323000b020081001c0348000004030b1151407503100d8914800c3c0054000341c100680d04102c6441001040141100c00013503140c000300b16219292046501e1f6901c1d081030001e4025075880041d9000941c0c0604030b01d031102800100741440400c15641540003e00c908441c60020303894504000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 394720566 1250 394719316 394719329
    0x1404060906061e03150e06040b01150203070314131a070309140d240204060e100c0302070b07210f12060506090103050a1d0313060e0105070807050c06030106091707 72
    0x40140d140d0344035046001d94a2903030f20303081a11011046c690031010040d86004502a144910440d4900b40700200c520b06000c3c100c4095410038021617002c83e0f008504000d0700510445c032559503d4601c62212240300c600d4201804d6045e0221149000b45010303030151504500c03a4403412034040d01c4d01b1040c850b464103000c0c0755622000495004000440c0086803400e0f1860700842c600c01040d4644240c42680c001d50064000101007940003401d914280c0d008070200c42503410504100402510003e403030f81c540c0c2c00f50b2131558600242c0041006400c00910344a5080c243d4160a208903921000303144407c414224400a01c445141c10445040c1c2d02c100c1c01143c2004101a1400640100543c05000e000f002d5881c1f0b00c3d521605004019048c4c80c1e142030241c034082c041c540d5007034440055152000f49400450400009004941c010798101003215440754203c0c00c07803501c030b00e05880c045242c0f0340056009500018044000140c00d0303041a81e0718181c485100c9103000c280c0640b10701c155508120310944 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 394721816 1250 394720566 394720619
    0x807060903120c05341202010c120e040c08151e0d08091008070807080405070e040206130801150605071106160b1f05040b0108160201140406090606 65
    0x120400c5000b000003c0341e8912030401e03222601022424040080000c04164400c2c1200e48111403040c686850720501a104807180310000035a1600020078448903040000c105420202c45a1180d074040c00d11443c4119004000788040080c0700e40050049030103964031312070074181c8101416280350401c880d52a90744070007003c05e48001c21204101d02210b2810044d145c1c00740400c4501c10503210200280c1505d00c194031041224206001300502800004040f00304210002c400c1c000028804100507007114001280c08030a501e172400010401d100310380054185c1d03031201c0381c006642281034100130150f905000c0307040f000740e546a800b44d80d9072040340c43c01010700000c000d800c40180303402005030003907240384100c0c401c01c80440d81d960410414151141d41d800d100c00701c03401e42c1e00b19400c00c090000d003100780c409000c000601c40c0060071041c0042d03c10441c1255221140d43d03014400d520450040000e20000002c6042a041c00002001e44601c02e580f03042c00c01002191040c1e5640d04445940740e4503044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 394723066 1250 394721816 394721843
    0x3040b2809020a0e07230c010f050405060f0f01030b0601140703020601080d0926120301060c022e201e21160203011404031e020606030c0d0204110c070807060903 71
    0x306c03540c03004040004140c0b2006000c0400189400d01c1194204540c040001070f85082900300145020401031960782030b400e03100c0801c4180c0d030b0000d4120341129131021403000f282d110100180e54042101e100b4580100000c60740b4014140d00241590407980340b54251500704070070400444914100d806a00c040c05144000d1180703046504443d26402000e040c00d840342c603840010b0961040d4400ea010340001010407161100350f240280f00300c5400c14116550054540b100c840c0100300442685c446028040c02040141c0350a0070705221221030640b007004d84180411040c07024500b01c80f02600401c49200d803404005d02c1d94000112200c4000780b1241c5c2c02d0800d41400c0c40780008a0304c042c3c080b601952900c009268008011222034002da120303444810504e9010407401c8040603807000803004660094083c083e1548000c5500d07500d200094610030004601070004c0360180108005003070940d4000603044a03400c201158a80c01e0b941c01e9415149110341c2c81300704136070050301c03408003400c4813009004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 394724316 1250 394723066 394723097
    0x6020a0806010816110a140f2e0f09060c03060603050c09010e09090106030b16020c040b09010504110702061620100c030314160e03070b03040b2809020a0e07 69
    0x1028410543c1d04400c550700c60656a6a6007458040c80f00420710030f07448905026200c1405010031880041d000d050183c100c0c01a049c5107040385401c01150480c1990382600701300084854000c0c0c02c54130f4100300c09010724944810f0060040c4480c0c030508000900e0000801c4640101c241204c2109005071358465000c5140340800400b1400600701810a6580b1480000044c5610403482e1082c4046c1c40719003500350a02c032000c5e041904500c80d1510980c136150717000c1d14694130b51001c1e505661b000d540c0001d0404260791101c0c068401e40001950028010480c0702c054460b00b0b00c01d0394218424114140c01402c843d80801c502401802d08541c002d039501d0300c60392185d100741040380c01c1902070328000c25858044062410b0303440e070030b480522030940c1024104942940006416110f000c09400030602e0b00d160564070540c41c000a0001895a9540b46c0400c00303400004040a2141c032030041500c00303158007242280000d001040b0100c2c041e802400000500e40782c0032005910819032903c41d066504081311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 394725566 1250 394724316 394724327
    0x905030318131401360b0f03010204081b1903170904150302010908030a080c090307030b0c031609060e04050a060f080318030102092103040308030406020a0806010816 73
    0x90309103070009086402c2100014a60207100c00c0c0f00c140200210300c65040c44040c0724514005400d0b0304103c4205e04010f9203040740c1250880c031119581600284804405c3c0006228000f0605a540d15600210700071491400118408882c0c1100204d000c1a580c01a0144500d142907440f4040c1d58144008003000464280303c0c1140c01101002c014914201c50400007404898980700c42d6100030300c0320f030410700c110f5812015a1000d8090403008504000d00e41c003004020020003899008070300c10101e594012a00d04000c4800130710361003500b10890f0b03d00b046040c5610741003194400c050f01d12158803004101c0c010110702e4143d40d010394070b06032080322100c103010141401510f08030307109030b44000c000380211300700421a000e072646002840d80d4540a01781e50150103030b900c0035107100f40d1041006189a9039201c0c2d5142d1039401000781e907185920356010282c2140aaa80003034040b400000030401000030715030080a80840b0f90700d80c01007a84610004540a0208032848a040c041e541d1031085081e0240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 394726816 1250 394725566 394725607
    0x2390114150d021e011b051b0a080a170c0303090307051209060703031805010e0a031709031b10110a080a0618020d06081006150e01020d080a1812030b0109050303 71
    0x6041c00540e50b081c1c0a00584210307034000007900c42e40c10a41030070031400c111408c030010789501100d03140702c014241a0481e071a4007040308010302a9118419050401000d54140c596401c46041541c0c0c036032400d079206980307a83c13103990300302c41e07900030000c544500070800c03010b0f41c00642d00948140d061581507a4250020721044001d01002c10b8044401c00000300c2c00d00030b10031070000040240084051501c3e0180219038070b4141032112003d15000c1000b00d440000507200e25035040c0d01c1541c55202501d0034241860000031003c0841c0b0b040c100294a0300c0790007001001180d5080d03495044940d11040704400b01c0b240c0e4000e2501d512a5017419060740803a603009026105884040010f03c00d0365a00b4592410581046418610f0f45134542008075000c000b59a00040144d0f0829074500c41110700000d413110942250102400713a8000070841034612680034403100130b80300d2100d10800403641018508138076040380000000e03060990215540d40308903400c0301101c002500035804c01200b07041000d07124000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 394728066 1250 394726816 394726819
    0x405010e04022205120703050c09040c080601030803061e0f060a03060e010906090e0a0b0f0403030603141606050a020a1203021201031506050402390114150d021e 71
    0x900c40348a80e00c00b490700812009407580c42c03c140c0c051070700c800e0059486030300b11000810740080c034041022900124003d500b511003203591022580d1145084030a08503681c2082e811032041c17070000310410000704000c501941084440e0785581d0a11203405114913544440990410520303006000d240c01c050010b031000a4540c100031a00c0c5403101800c2d091000240d0020020507200c2c4810040e80130241320b460200b0080e40c014141c2500d8a444414001902902a9195040f0b100c006028107200c1e038421005907034411120b0b200300007d170400569802120920329000d002c01d030b40004600d07000f03600f101e660040e160003a00030f07410140c8501c0c0c124860800c103841455000c00c0b001490102e00006c85000c0c5104117111b11207481d141d13503550201e510a4100d035000300d10401016460b0383e0708504504001084040c260120380e0151341040029100d04080310681d8204110351400c4294030035907a01c41e0a83c0221444602d28030801c0050b00240038502035080040400f941c108075485901e4030508a80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 394729316 1250 394728066 394728071
    0xa18030f050d020a03090c05010309030c03081b04120203070609050d0602030a0f060b07050c0f090109020a0e13020714190308090f070b0703120608060a0207061d0106030209100b0405010e04 83
    0x1207082c5140240da00240480e40000d544903c04c10810841c14150b8003d00000c4c80c0410001450340d801400003807862401a051010310b03400a100d14580070103804014201c3c0708065140c80e0744500320060381c000c14030700728801d000d180000318590784145140c0c01120002440c0440300e800381e4503508020742c40503040010094542035010103035403484c0241c2d0020301220041c207942d0651800c1c01030030041100982c0340305046d0001d0412050b52106070040c150b5400c0040180c1c0c03502410303070582d4581c5a40c10040d030081040c107015803402105901a1140d80e000e900d04075410180c92100301d0300c4201e806c03108c00300d0403115400c0700b011074071403040c0c1a4483e400e542240d8000304403115203460306500d580b018207403d02c00101c440405921000e400503180764400d051042905098407e070b120800103200c49007084e4049002800c0c04213580000d12240b6140d45481074600001d56020301070602800164010306948020920f0100000e02c840c08a0b00f5042440d407d040c28500116050414510394070f62054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 394730566 1250 394729316 394729327
    0x112d1b070504090b010503071401020c060a0c1718010c0b0a0b030f03040806070e0d0f021c06020c0106060207172e051501020609010b1503060d0b0405010c03050a18030f05 75
    0xb140e511030200d081c1d0013841e40300400c0d0f2518040600d0f10802d604106407040d1115400b02c441d980020f00e001c46204101d03001510340d04070b504100c62014200794003829034030030100802075055481c0003c1201c044c00f01200c20350591000015200400150350003804404541d000440944040c0d0203200706010080560300d04498414100b499134100d9041155581c01c99818061401e4200d02d101d20300c07080950f498810f4041d2038a030f4801210080300080e004425400009800d240310380518101141e0100c1c0440d21100d03564101c60080c100b50084001500c2904404500450010031040503142c00c04010710064001041000320b00f01c520300f807001440d8400002e0b030072900d0b00380141803013480500d09008440c1d40c0308000a1820348007506260036a494415041280c1c0c4440d0341001e900101d90054950381e44440700400c4200c003507950f0140001510006000c10000d040d0002c0c00000d003c3d60303081c4807580b244804074089503d00c00b4140c4500c040801144006401203500b00113048240c24901e0030304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 394731816 1250 394730566 394730569
    0x106030b0f100510030b010207050141040807030506071b140a080a0806041410031e020402040b1314100f030e0f01232a0904112d1b0705 60
    0x440c5804c600001003500c4014030340d11541e04000307401c010710091802e08407032107404031701c2498580071001d0b0402019071300c00c1d02c04c40d90103803040f420021602915a29502c0d99980c0c201030f1503030a5400211101d0183c00046202c1c284200c0c0e5103050510b1400c07010b601145070f0780c0c5003920b02040d1000004c040c0200d15a507008182040c001d0540c601580c0c07140c1d0350501c0d110301000b003100d901080c2216091024024044190510380c8890180c031f03441492111407400440c0c10144241048000a51260001601250000c0040054001c4441e02c20582c00c01d6525054003011810b01c5042843d041010a1300c1004130030302c14400d020952449081c00500301c1d05881e45a428020440e007003c1d20f0345e458403a61000154006812500c202040c4080000d605161088480300141200d011049895034405400d0481030f440c1203900c4c11a00400070004400351000311a22138100c500348500c91904c134402d000e0b0260402000b81200000d40354050f10f8500c2041b8101005800c043d40c94040d03104110700800e15 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 394733066 1250 394731816 394731829
    0x6090712061d01080d0206090d0c030e0306010f0f060309050d030f140f060307140906040c050d02030901062c01271a0306160c0f030c1e060b030106030b0f1005 70
    0x41540b03a4840c24010360500121900c1c2c1182d41d5041003c40d03010300c041010040d800300d044800541c141c43c0001d004910b81c1411284491526006603050081100006c1d0b074a183c01a20b10441d0102c1136500fa45640e245015011507100b424054a190010040994020b102e42c1c800011910700000000303110303160703083c500b00701d03902254500c0215101d04144000c610301004803200611031a489840c0700001d10000ca00c0144c009000540100d455400706142c260140c0103032111804010030454503440c1c8407a18501034a6244102035500f07403191001807900c0d0f0400b9400c0710414048242ca41242d10700240b16a84403216903089400f2170305414604149c0d0918040c800c0601d0010b1604945c1d80c0c18030040509080d0007070402c5800182c1d50310039600c0c150300a18002180d5030071a2070200b41040c0741c101555008041940180081004070458611140000b80408400e0040d0001c0120308010f074281422035101c4d0101400e040904400a90560642d03403581c0c0d40701c0807005490328980d0b62480820314 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 394734316 1250 394733066 394733099
    0x20d061407030911040605060f0c03070b040302060a11121f080a11130e1e01020d050703091523040f080a091a120115030b10020a060509060609071206 66
    0x25203c1600c881031007050329540c40c03400011602001042d1405c07000902c00c2c46140c229446c0c1c0c0030080340d000d411403024010f40b0600d50300251001c2541c6890316009403a00380803549180414604484c240c46c540d824030644e00d0144c0d0b014000101500e50005c81304001d14141c18002c010300d00c010b00070610a809000c8418001d01c91044d07150301110400c2002030901441800407451441d0020400b1343c03240c0040d0098509440001d000f40d8022103802c02d6000e48299284100301600305024000c1e1580d0540c08400094040c2d4510722a11020f09403000070fa42c026400c141d0312200d103001103043c40a9156590f82c1240c0308680f94602441d00f550754034200e4208070340000201703d88a40c20009000301600444c148003015214a1a20664440100000c0e00c1130041c20f444c0d8147c0403410302c09030300030760091481c03d00083c41c030040d60760a514000d68504040d842118100e04200c00f01d20301402c0000c142c0d02403d001860200c039540c0d002d10803186a4900100e400c0642e485150010388aa50320b0750404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 394735566 1250 394734316 394734331
    0x809010c14070b121506070308090102040b160506090a050303161205070519111b1306090506040f1a01110312090106090c02060601021b0307080303150102070e0f04020d0614 76
    0x15261000d003100107103014801003009031700e00380141c0c1c0c03015a95600070484000f140d15040c04041030301c9a00c5160b0080c000c9800005421000041d01c254050002e0101c1e210144070304110352403540e4035402d036919a00c1d503c030000c290764014804a204179a22041d04c0782100000d2400c00040f5043c42050f50642c0c10603203180010a50004003620302617001c03c819a4405050300344040e01c115a8141c003940d03050301003074140754100311404240729a524070b813102061242c400414030030307151101c0e901c1008203016145c99100343e00d405014001040c45005402d20240d508481e40c80340700901006603290618090091658041003290422003c0c090b04414003c0622800001d0031508000a0030201c81050f41c40e0130a6500860802146a82c0099240441403945440c0961154144042845c00955030051080c81c080402006808070b0082d28110010300241e080328138296595990b401d81e16025641c995081802000040241c10454205c4141030701c902c00000d46030480800c0756111280c00c2c0c0b01c42c2d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 394736816 1250 394735566 394735589
    0x180204052818290108030c0304180b03100f0b010c020d06020c01021903050103052e2007200d0c14030c1e010305010806010b0403020409050f2506020a0809010c1407 72
    0x4a401d8030310082158051700841c0011841d017889200c2d0f030703907880c040c070b1113401d20158030007a10111030941a041700308480c901030708031640f00300e07030071039940142c0341907442c1c00081407409200c1c0109610030b0f41201030543d009000c03d6505100b40d2202c030007039400110b00e0860356400704a10700c034100006180e40070704403641d0740008455046140542c1420424400014003c1c2c088020418140a000e0003860100c01a1302c009524220100105240c8810040f020180000819844140144e80306811480d080a824600b180d604071000c1102d09641075901500c214030411052181046103403211437040c10040031100503900c0d08000402d202c0c026400c0d404182c03005094802c0b03a5815004050140152501604c0250704101c41c428460061b48006441107450300401c8092060500c1004d0600b04e95109403080f0005c5840d82030103c20494517031140e2280490400940180301003a011911580300000303d2038001460011118040303603820a40300c1c0d04580c10801a80781d0104001401054030740641d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 394738066 1250 394736816 394736873
    0x209132a05030102130e0709031202010c0207081b01122007120221160819110309060a1101020d051617190504031101180204052818 58
    0x222011900d5a9124901070303801400400c007045008100d5600350751001991500a50350311404403003135031300c6600203401c06200108002080f58190055901030075243c003100c07021555140141e0340c541810f40b040e120009071004422556201d180d5101500c0c0c6003c0c3c02007034250410302807424090090000d20f9400d40c0c00658034040268101d011138644205001078081c4901011042d0002049500741c0ca0007924001842440039807851800c5040903007241501d42c68800c46604440000466540c04000c1103c24540f042c6213203001049405410000d091a420541480b10944101101c407050b1000ca5400340310700b006503100c900c9910311502846181640d00c921000c0c0240411906d20b4120308007440b064200070501d803021580d002005620b031400156a41c42d420100c40007211000c00066550030704400800e001e034900941600c3c81c0c001c90701000603443d040002c400c44008100d000a40203000040381e000158250320600c0d094102c0c820314907c48045503100034000349660840d158890710f0050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 394739316 1250 394738066 394738133
    0xd06020408010f0605091510110709050103140d0e0f0d1202010501090506060c03030613060f0602160e01051c0c08031b01150506030a020904110a0f170c07020913 71
    0x10f01381c003c1c081901c1092041c00d01000701400041c40340880307405043d40214910380588030380f070411160a032403800d5a80c45611400018040e09007071005981060501c0c403052003507034000c541c44004800c0d64484000c0e074000c00091020801c00301d01603980c0806002000b03c0801e520f00c075800b41c0b41c0b940e5400041c4542c10410880200c51010b419507024000c280014180707241300104594102a049900c000b800d8401a003020141080f5000a44035190454000403556000207030720a4a4400240b11070f00f090722004084102d845c2441030350387c42240100105410007801806031102d078012960551429182c405003032865100c08104120fa00e42c4490b01d052060742807046040d003141e0f0248080b41c051400b000100c1a0001900c0e8214059000503241150b030b869501950400021112603500d0707004500d8007078a03150719641084041130200640b1001d6142d100481c52190034400401420441e0b29000c0c000107000007080c0658407040c00d039a28020030802c426103000189030901c2c44021549804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 394740566 1250 394739316 394739321
    0x50a05060306100b04050603060d020607080406271712040807060e030a0305032e030f02041b020d0f05040f120302070e10090507031d06090127110d06020408010f 71
    0x200340400f0090001c0c0d042c02420900811642192812590a9169216038001810302074200c00b00a511010001d0404200f20810001d08101d80440d120550500140d000c2148602400b90b00701c1d0042d003201c0e13410302c4a035140c60000d8406030750a400303c680310a503407003122905620a800c0380300d050703010400c2080320681c000c89651980d1410b03070151010720025a8043c100340030150441400076081d5805904103511810351680c40c584141220301e207503542e8284100c1040106105034000c508080c03075004c208200e0202c11004003502d9005100f4022880d40885403803021b407508104000c0700b00000144d0702030b81050807010701150203105100040c145000f2b480c11885500000c0940100000c02030242d0100b8100e00445244000102d1703281d54580c0110001c2540f442c03a00d014403191700558120880004019201b240100300800040e118010388101761a9400c402d80e00d10308585400c81d0024501c0146030403d00d0015081c841e03e001c1035a1000706a801a40244013140e541e82d85001c03a000960 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 394741816 1250 394740566 394740571
    0x109050a0e01240b070b01050f0310060603090209090a0308010b030720070609080d05091009120f0212011107021009081915050c090d05160f0311041b0804080409050a05060306 77
    0x1e101d139282490564540c00200d405206280c0b00e0b100701c100200c0c2c1510180005900c2525249040258a4458001400821031420103030b0062100c4c000180c150380c0f000504117001d9404d515512a66031a141d00044164402091482008241c0240c006180c21080d141500c41d52207a010b42030071802c0910007030820605a00c000f0300ca5100311031030341e9004c0d004000c40d034074604240c03118203684aa0110980d6004c0480d400100d8001f4070021480901200030155008144215600701c1720703600d00500d40d030070b07240d003031068000000c02003005030010f140c40012820f80f51a2410002d800d40d0384c80c0606402c11442d0402440a481a901c0f103408001d0b4080855400e0300108108012904059507207c4036802845403903805201c00c45001c1701030090801900c203003141000c0c1e24a01c07041d10f44140c0b03001c000c1c0d188000c0710f8081900c00044800d161900800c00d00401c1e0015405103060210360072a90184040e005030b840380d84c2084041103099980c003600344920784146012600f030070981305151508200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 394743066 1250 394741816 394741829
    0x21b0307140316080325080901140106090e04020a03060507020f06070206010b03060111070902030702070303020123040813030f06050603150c0315130c0e10090b030109050a0e0124 79
    0x8000d9070b0303504803d0301010340d0826002000c8503125600c0100b1220a000e0540d4035006000d281100408456030040700584501b900800901c220202034001000707a000078002c036000b00300041414007051007a484200e40c458001400d0110b449e44e03035103c0c01c00302c4205880010041c1c014102d01d040001d81000030640103402880100401d602d000d070142d0040c00060899810000300000042c6030780e01c10403072440503103032044d0308554030700304218041e54440752032004801650800144090b000700c500c00403402d0003552071303e6002e83d50702d6540d00074080d80444008120031400c01c0c40800414200e8450030341b030f588610360008240c11300d80c003051310b0207040403042c44500341c02c03008001c0008009130075203800403040740c42c043d10420f904001420301c890f5500040c94051400991007285075100803070744100301c000e4500c00c030b0011840804958400140c003074040c1015040004104100380c41e400b860340032403040da0016181d44404580c0c9c1c00c1d40c00340c00c100e065030401d500b03d5400a901281104008090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 394744316 1250 394743066 394743073
    0x8010213080f1902030a14070906080111030426070c0302090f06010f03020c07050d0605040b060d081602040b04021204020108070c0201021b030c0901090c020d0c0f15021b030714 78
    0x14082103443d55104840c000c02401c514680200c021501c080103a070b0995a0701c42001e807109041c9513000380c0d40d00f0781031140348aa1802c15000190000042c03041450f50403a013a009450b40c0d803a52550b0f01d40030072030700d50402e8004900402401e0890b40d2005412028030804032600b0390b910b540104101000007415490703400c004032080c1310040c0c2c1c12801a000c550000e00300982c607601c1c100d07001c0e4140707030840d403051743c0214217aa040010400b03c0ea00a521892194410410540b81e8400307212807440c0c104c000400d00901080f4200004a81074880948140300910100d280c0400c14085810398000e400c2c030014099030982808215a006422260b0010480c50800c0d483e0441e40c00007996010031611304c006907082a0802541c6171810f100d40c4044010180400c0310f50350b540c8100c000145010420f01c5c0042c01480041c981d410702c501c000806140e0403100224001800da22142e4100300041051640f10345d01b000903044488450004181b5440f00300065600c40909081040104805959402c001d41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 394745566 1250 394744316 394744333
    0x40b090a140612090c03030c1501090506010f050d15031109062704080412030909200307120f11130f05060a0c2f1309120f090b040801021308 62
    0x71610020340351038a440c00b90f0300040784c1310792048600f007210003020280c247c0000540386425000c0007452120041d00c4e00c640e10100c2c4e80e940b030038600300e600c140e030894001184110b4503030000340b00c0c002910071040036407400140d240162803400740c881015842100c0c0760041401c103c000d07160160b4207a9110340706481984d00c241512252080c070110340d00012503144183d0340801c050050010a880c050250301c8060382c44520682005030514100744502c455150a108807440d078035031040040c2d1508440c405005045031500078041e10248040a4600300c040e07a103160050100400340a010b5070364041040161b61800a400f068998091503013100c409070342c0048040040d0781310f40e01211030240a500d00781c4280e042620308414400d0449400104441040891701440c241c4506582c5510004071052208070100801d941d054502c01070025004541d4190100f0711140120150700640c0c40c0c5142001c00140c80d0381c8104000e410640000880c0da502081c0280d0081d09202d403400038140c4440200200d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 394746816 1250 394745566 394745569
    0x203090301060f1d190e010e0304030c170c010c030507020102250f272705071805040c050f0604090219030501060c0c0510030e0f1c0c0317070212040b090a14 69
    0x1c01076080d64000c21383c6d40800207044c020030743c4800000c502040c181c81e0f40319a2030908047d030604a0190007100659551005884000010705140c0a04180c485002101c102e071410782d0142c10031340c0300b0380c19030052000d02058000c0486061210311170403c4881809030a042c24501000d1854102d00d00c401e010301301860000c41d141d058402a84207004c1c01180303e900d01c1c030306080591000344130000300406d440f0031142044808122502502c0e1104d6100c0403c910608904065400684007d4090f00c00e0300810b020906280328800d0040e100601254645940c8000100403070348150b180c0c191000000100d00901541030003414010001441c15043c1501e46840b10244d4a2852080c1840b601c03009032044000342c0a60801a005001e80090b07641c00d004030011281c4a0a501c110446010907000861911070701403245003e503036401d99210000c907809501c20610415000c0c1256007580300b209003c013242c40c00e06000388003611034070481944548103030f0b040c031020301203a4020000d01c000e40c202e203003402d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 394748066 1250 394746816 394746841
    0x1b090f0509040f031701080a1115090d060209150c0105150a0b0901031512020f0a08150402030a08042403141302120115050a090b031203070203090301060f1d 69
    0x4280c20051106030a00f035440c0595203100038451075000c1400041c0005070100d4003040035003005000d82c140441026165041000c260300001c450054498107020a1384c0358240310144c285180c2c03041b4030051038040b1000001d42095480b5017401d11401c1c001640640800b070a00510f6001070600c403403080c46400403000107800d01e0300f0f4003030001500c10101c1c524010f688030b5040402c0c2411003a1580340350a80340d80f21440031f815250416400b40c150410002d900e03040003000702c002c035171440c80236003100402c0000080e01444040d1003a81c0c188a48bc0403800411004801480244804544841d00360ba445005000d00c01081d4600001d261402d90400305241e00440601d9016500c1300d000307010302d071451000801f55412031842c00410f620300101e0f04007040b90028490291002211281c0c0ca00d9034840b210825a00d4112071250542c2104490039102c42c011005950400c2182c0181c0382401c901c103000c24212001580310700107448a45204028403111002e082da000c1c2c2c0c1c0700e41e625a05141500e00c2c2c410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 394749316 1250 394748066 394748071
    0xa06020a03052104030503160c0c05060a0509120c031005160e180405100b03030c101116050129090c031306020c0a0c0803030f0402221b090f0509 64
    0x18440000b52504041030520b0700030008400301c1040f0300c540d00b06418024029001219a8002d002d524103100000601509800c1c1d42c056201401c1c120150805080c020117400900b1014103121081c010000265a80c200c1c0c00860003015005180c03a4042c8010540b40c8140700540041c00c40c03902d81480007580c2c4c58041030b4982440741c1400340386d01007910086405030b40d10b06a00304c000a1280103200401c000841d200390516940c4009021100060f400c0544900c2070366201c1c0100d034090341c072042180040380c002d00c20071071041c040d036418034026005803514020418421282da940d43c002d06000c51101a0010000700003044c1d102d03540e042000003141c14100c1c0a4041c44001c04084001240821406100c81e90142e2041040d504d450703514403d20380e11101c0d4202241c0c0b100203620301003034070500001924890b001c040000d40b2580c0751a000d1002c075104080c1c818160140d000b0041c1c0381e201e520301855881f9011810085200c0801d09801450700301c80d508041700c84240d00d40200003a070380341504140c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 394750566 1250 394749316 394749323
    0x309050f12030d0606020f0f0718090213020406021908030609060418030c052e0902030c04140a050a1e0506060403120804061b080103060b030a0b010b180a06020a 71
    0x5280003900018019407020a4009061000094084491a183d00020120b4104d43c007115801090700f051583c551000c0c442900081e8030518080181a0400103080d4001ca1445800121203059401044020103000e450b125910340015040144c1030341040203d1041e10200c0d1001c0f040c58841c0c0e103454151102601041c400d500780004944aa65658441c420b9407448071f42000340c0c000e1514001d40310508818054590b80201c18410548040c0c00c182c48103600e601e0604d10031092902c000003c010001402d050340c040c46403482c156401c1d01d0300d03c6224411080c9024200541c540304c1c41c15402e842c2c0c01040e15804a0a241580815407041409240d02c1c010522000c01d81e5a030321404640c05000702d0b40080e2001c0441e803220382c0b11035003254849018a01444080c401210032159200943d41c202c000c0d00000b4075000300401c0800c40a601c40c9003155001410346103030380929200c050603108280c0090304503040001d80394000c0e000f0f600300c1c03095562040e0360b289016403405502030b44035548044041d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 394751816 1250 394750566 394750579
    0x30305040f050907173301091a0a0c082208010b0a030302032d030403110f15070f0201090b01090b040b0306090709150e01080109030f08060f0103020d0b0a12060612030905 75
    0x11006080c000000c07000380303904021101d404a140d10919199400c1b00303152804213000a201080a01c6007028100c00b0304030002c200c515020400604231a0203507040d10607100300b9014458103132038017051030380c0c0860325515401c1180140d00b0b1440035800c491240418078403503610078a0800c002034012081c0c1311242e40010158010111508012200900c9404a817107120400004c10081507041428090701220020031503034402400b0700c0442e629158190a15100400240000e0503507120361164550003443c1c4c80081003a542c0c2d40c0e1640320365407080e0004c0c0f4a0580f91001c40507141418841d0402c0e070f88044008001b241090a055504c0d8009805500360040d1103100103110400094058401021210302d0441c085da501c50295000f8518441c040700001c12140844910a101c5d029a83c0201c3c40102944504d42e80030340154025400b60001411031521031074007100603905c44030101c00902c60300012100301c107000c1c038151080ba0a513821001070841e003e1010004254000001d5060301c000b0b0310340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 394753066 1250 394751816 394751821
    0xd020a060506040609060e0126150c160b01140d081606060510031e0501150c060f1802090c0c100209040b041d151504180507030305040f05090717 64
    0x118000d40650740109085c00d040134000941e269040c0410340c101c803000540c2e1003e0340900100c02402404580b242d061a1f400440041406c0c128010540c0e08512052a03580ca80b4540c40329025841c1301c070a0302525400c902707400401200f542e42002034010300007118109003101441da5000030354042c0f026126000003d0300e40c24000c01206034000030140c40700404400e4074000501004002d0583e0000d0220441101d00340d20300f0b1341c01c1c40d004a9068980140c0001206c141200e400c8951221140c030950300141c8502c4039029006081c0b0508210303090300c20340a408052a0300622110000c041c020b22880d41040140041d60350021480c00003996403d4009603840340e0b00c000140c040e10180456a0b07001e4030380803c103540c444103200600c3c0c00b424098207070345022a10006038442c070f40c070880310880359020b1840c21112500c1c241c1e0101c00e51401d0b01ca20900d010500c2c0e10b41514000c0c958204501140d0005800e20990480800300002801c040302d2502440c80d02020090680c20002400d690052906c4007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 394754316 1250 394753066 394753069
    0x8010c0219260a09090209181f1202090f010e04080714070e07031a0901051c05120304030908160306020f0d0908090f040203060a0b091305040c0e0601020d020a060506 73
    0x34540109104000c042e060303010510041c5a58003070304100003c5160103c000440c9250f6001f81c8040c0c10006000002035540700003007420034a40248068000c44043c0d01545070b45c000b41020b08007908003249418005021031051100d04140a050044900080f0b00100700c0700340d21402c0c07258000d60207403119840728002d01c0c11290001d180750441c05240942c4201180200c000d4110354483e200541e4140a8141d07100034041c19556910b0409070131220201c010700450410405000751440104c010a000c4400c07a00c40e01d06010000e420700405010020921081c1035000407008054219040a07181d144035103100c80c14400600c6c0710060006402081048146e424103003560000000740d4002d0220740303154901000c3c1503000122082c807030a441201d0503402e003400d00c01d41e0710945020705100c00386030800300e01d03282d10f4001c0a074417544180141a00440707031a050007a40d029900c640701080c500c40c18001740f60222540113100b1750455000341d00d900c040c1c1d68001101d50607180c0204000409440b80c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 394755566 1250 394754316 394754333
    0xb09010909030c0602042c091005100f080303010311061206010e0409050d1101110c07090e0a1a010504230a0c0201380907020307120c0c0801050402010908010c0219 72
    0x20011346024400700300010700d0103480150030040340c5e4450b00300c840d401e605810008100302c10740380140303030398440480b22500c0409a800180c00800d02c181c0781c403030562350320402031010a041d0041c04603030300003200401c00c0090503203420745001e004a40c618144010690550103001c1d00405007810401c94445e4a011a1142e6100c1800d030b0360842c0644801d08408400608a84802c6a880c3c0456290669100075018400705840506110002500c1564035200b0035401401030404034150600504c260000001d001c210613600c07001c49100070506961500080008840c9110101d00102014440400550f42080322590340010880c0700081d5800240300101c1c010301d507901c0001002c80c001c0010005842c001110301103038481e0215107251402044040c0213417400d0541e101405a4002d00081000a0313018040800070083d61402c2503a5508030b865076012640c0380e911002a59540d0030502c02036580c0440400080c01000c1e00034020743d440074100a59598000701804050b15501c0444010040b1741d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 394756816 1250 394755566 394755587
    0x1207050315090a020c3d0231050d020d0303020c010605030f0313051512090c030a0614090a031b02150a0e09070c080304060f1b0216090b0901090903 65
    0xa414031160345003c2002c1002540b000e140c403c1c15105040340600001060b5019034002c0fa540c140c8041134200d1b4500e01040e04056609a060490702800701440104000005680400c1d51142000454440e0344050380c0e06661508114001e4608003510030168644c20947c1e00307050b41c0751a00681e21110f0180c050300512064101c19818040c460a180030203500001420b0004c09135080181450396910401c56501225081030801030001c0c041c0c03464404800e00141ea00c240c204007a10484c0e021180040d09201505400301c54447d9658031881003100c110b1496680700e100e00000b80040212034402824180208040380b100000c5110182c04548560148147c9508440491901d4101c148006822450740030304043c01851a440065002440b034041606102e070000d8041c0e16548994540d540903010441c00345491580741c0d1940d0000c442c00307041d003c94a10b0300303902905180b0401c180c00013130301000303a10440020f03041001075150350b0b540440140c110740414000181c40d0300c05140640700035000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 394758066 1250 394756816 394756819
    0x120602130e0a0f0e0a110a120b10060e0d0215040504140906060102030a08150f0d06050106110109032c12010506040501060c0f030e0a0f03051c03021207050315 70
    0x940d00009041000e5000c00c5004214042c002d21001c15040440f01c100d810329181d150302d90b800b034159803021840601069900780c0010705042c1449468202d90b80665800e000c0c21682002c1c0441000f80750540010000f0203800c3e140780103c1d203500190f000401c0040021000ba20940c60b01d0300028000c0c9410003210300800000c0c20a020449006c0b05490701c090040b04c0d81c01441c041c0364005840c5600c0030088030905445512062075030b46402c554408040c403076050b01c0740c111105500c08155036035115081d070b00061050101103015810410001c04980f100c1900103403036814900020000f98108155660740248035800d154060701c0b0454100c0c407001c3c1802c849030800f1130114044400541904414442e4206440a12807640e94900440d40c10300c4447d4080c000b81109846440000d1298403100403c080041145021039212001007100c040d155204407070301e5200001e01070011651218034181c144441c1801c600308881020700d9901110010421010424008005006510200e402000780b810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 394759316 1250 394758066 394758097
    0x17060112060e01091b0f081b0c061e070c020111011103190c020d140a02010e0607030204090e0f030301032d0f060b1f0c030c0203030d2f04120602 64
    0x103548484800d840404e0203003469442c141031400e40f0003a422a0402c100c0e220f155500f001d00d038500c04080f212580040c000400710900d008080b5450961203001c0d241c541e2840c00505a181400404500c9000d00742c012014805111002c0144080c2c00c550310103200c503020709000b0f0000300081d00d00303801010413807a0300c00c45a0011041c000c590641d420a41400441644100030444040005980d40e071034100ca2400041c0c190a204100e0221501c043c10190301c8a00012035490b100c02021402c00b502260800d001a5020030200b0070034002c0d004007031207a40c01d00050305c1c55003c80c01d40345031607102c14000581401d44030601c4980e1050558100c10440c512400c68656540b01486c220300d40c034400c04000d50365642480b8003a182c6262003c03429110000101000000510002091740d601c0c040f048280d052010155000700507803814002811910001c00c800190041603a410005880310064403c041400d400500c1c0c85408100080700c040e07030f501c040a5000d0a0040c80d000c000381c45480140c0e2024031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 394760566 1250 394759316 394759319
    0x50f0a0e03011a10141b0c0405011e06030b0607140f0706022d0c090a0f05010315060b120708100b0a080609070309050a110a080d0c05061302011706011206 68
    0x6060b248091108404469601c1001c4d2030400454040686001c188521241000071000c09110303c0728100d074200511058a030503503a840001812100300368858010912840160344644902800d45c8000e4a282c2c103080006041c5000030880b517000c0c03070328010030700d00d00703410195400d880c100b2411101c802d01000b118495034654071b0003501c4103042456600c400e03d411000034000b504101400c08010001d0008217030002c1c1550070003850f03060241c8500c03002c695072183c40500307150b1401018042d50203400b5030303000c01e030380307280144221003255010940c16042441302124810744c5d02c0d2456040038aa1a01c1d45440c1c0312041481e40d0f45070f4903440710400c21000180c2481943c0c1140b581485540115046402d9980c1e100040c1c0580e0002c1c403008019400888607680040d4080611400f044c01c064804140c00391101181c0740303044c070b40c40d011501148420206008001c41004100c1d403100c640c0170311001403005640046c0034901c00444520507051300000061699100c0c4c0101c6079070303000002c805e00045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 394761816 1250 394760566 394760591
    0x409110a0602100f0506100807141b10111207091d04050609070b0403170d020708130506090d03032307270f120305070f0b190c050f0a0e0301 62
    0xd2200004881c015814403000300c100302c62501c01c00344035046c0901401002c00301c03240c0c11181c0510080c1058188850075405407400815800030b40008a1034107400108201c8140f001807401b0700c0c0801d209281030902d0000d00020400c001a510404045c1d01c02002c0e0740c56055003501d049296030042e02400c0f10355100181c2c1000c3d500800c0e4007035400b4005884441e02d4503414a501d404242c0115074046500300401c20000d0100010360f0001d1141041c02c50034814008040c100741d80c41103000703070340d040008941c1e00440b08440000c90007c1104035001445d0030f0210011500042c00000060f003850f54400c9208643c2c1046c50a00001544016180e4058075100c180500300150801034440800140d08245c40922454500e0800761030011000b021001d1800030071402d005c08280089082010030301c108000101c0119031122458812101484649000d090070f500e80c01144080340c101c141000a0612101c2d0840103d9914400804103641d0307400422105a442c81e201c600a650190700c0c00441c615203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 394763066 1250 394761816 394761823
    0x2070b04110a03021e0409140a210e040e01021204140706080c03040b0603070314061b0901080a1a030f0d0e010c030e0d020a090c02060402030106090e0304050409110a0602 75
    0x35445006458012030700300382401404080c80c040207401001d941800c603003040110700702c2d03440944003d0010034000d4840e40ca0702804443d84000c00000e52022820900b0050341e18a079030300710000803c3c550010303407203e80002d00010030440458041c40d03540c0c0c1000d540c441d082d0111000d200d0b000034a4201c07400d03d85041641e5120002948000707014500010460901c2801c43c01d008d410345181440c290303111915042a00030025000d01e41c5403054000020005100c1c9401d00c0450035454054195031821904480c940e141c043d010001105013000b0b9007580380e0704503806540204102070300280810301c6a800303080a41a00503a164144903517102d11100f2000040c0a0544030034a58034642c2660042c40150b0318001100001000305484001003c66810032482e000101c0c0d000800c402042c40c1e0b1800130804598090b41100f00580100c0104410b504003400341c6801400005401c01007000c00c0301800362640102d0241600c15900c1e00192018880c0d01e1100c07802801c0c0c021f01d46400719a41c0c0002965 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 394764316 1250 394763066 394763071
    0x703030209031e06070c2a180209010810150311091c200901181b1d0a1409060a080d050301030b010906050112090201120501260f0c12010e0102070b 65
    0xb00740700c0c3c4000500034910405040c00758035071021708910041c60f40940b032000c02c01d200d8004400c0340d500e12000105074000340c81001e0441c1041c8c0b001a600e00d1078000040407008010303c50901d07411058000c200410700c00302c0c00c0c0344030b0741c69240000d500103507400400e04d5407044c0702d142c83d030107000d020f01c100d104c00940745600c1380300307104e1600c560301100c213100502046050040c51940c007c00100040000b02c442825400340c10701f0311000000c1c45000c921001007100c0110101e00001154081e40d03d07440120228048603403e0115000b281140c9030120080c083c6d032281c242140100c1d032200110f061600c1d8560301402400618042d6440c0040c89980102a0f8100b48000c0e62100036050000030682c04c544103010582c2c4041c0d4410b03030341e407415a421001a010200c403c81c10080012401003c0001c039218250181c0101885d41801c0c00f20b41800c10b12460a031030f2422001c2c1c100c6450080388200024070b100340408141c40100c04a401d02c8003041c01001021440d1a003035000080141c20003440c41d0b1900d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 394765566 1250 394764316 394764373
    0x703080f092b08101a0a0203070b0a090b060f0604061103161101020d1b080a0507060f020301090e0105090c1002070e010906030204290f0f030709020706230705070303020903 76
    0x45580e90380f00340305150108a44110f07aa4501064000045070001400904d40010306c1d004503880c0411994901c0c00ca01c40032201c1d0015955980c0c070183c1004060003c081c3c010b40202c5100d9038030152440000d0300d074400d030700c9a0002d003c9140030041d5441018801e0310707003040800d28000f024030400d0811188803411440c180f4014000c2105030890b02d806a42400303901860b034605e0301903590b0700c1d40c0c4281c0c2e240e10209005040c00800d1010034000b070242d005c2d030b00725464500340168a039403400f2140415a28841c07000041a41084208100c582c0c001601500000b02152104080b07503484200341d050440c42c0c0c20113400c15000d00004a0b01e503500781c0000c411030b40300350f900300300383c0350320252000c4001d41d042904080403009510001c440e241940c080301c20407200504100b4500c40317400019181480d035501503810700c4d8002c9501c02c1071107142d102e0903224880803040094144084c0500010260b4005c081c24180540800c4003400d0504c40e0b41510080a0302408070380b1011600e405101d01d004074070701b01f403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 394766816 1250 394765566 394765577
    0x1403130203100c02011803020304030b06040902030a0609030f0e09040b0703021603020a030f0311030609090c0d0b01090501090203010b03070f091208071401021e09150406050409060b0703080f092b 86
    0x700c0d2681090750a1b0040e038055015604080c1595201d09400310043c0001b0f40c0030b91143c10380c50141e50140310740300c0203a1103211300040c1c8644c83e15002d080740d074020f10300d94140040c00c0300082031034581c803d0307065000e03900c1801050142e5440310207400a01407141c00680c09020104001c08054000948002e098081d44a00740d01c0c480462046060b540781d0080010700950a02c00308640341400c030305403900a000c1c071050300c00c541c0c040740108160001151003070341c0350030b4003200401c00080c0e14421035001d05403140c030941c615818503803410410b00c0068130000800011322485601d251050241d8009000603421003480d030400390405040b1900300ba901941c80c004200417401c1c09410520032620041c85005610700c0b8240780034070314251904802c140741d8000008602c0d07003108120701c0340104007625003522295255824501c1c140c0848029400c51003000504001020120350045c02040c1e2080c80d0104400e110740d540c20030306061030259100500030000c3c4445d840d901c1c81d0f10440303500d803405256032032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 394768066 1250 394766816 394766831
    0x408010506040524150a0e010e150313030c0c091e0501083a02031b2a04090f0809030f1606080c0c060403030f05161403130203100c0201 60
    0x401c411900261092030400f01c108041d8003134000d4401240340903490003003290140c0380325520800359540c41200810001070900180310351543c0c000b5525a16800f00780d401c0c1d0203529002c96070011072303c00545906250849036031300000b01449000f2240c20076070322607856107c8a40e11103d010141c01e44e003042c418100700041581c4100d028500c1018101c481010050401c280c0e411001800c0c8412154103100442c019441c141e440d07140748e00400e031038000a40c02150340741089220040c2c0c1c82c0d45402a0320098210800140405c011000b801200390016503d4074482440f4400040080c0b51011000b450380814043c49010300107044041d24104c8025001d0342d000c100801055600e44000440b5441e11801d04503003444003511039031003981e2002c5140c9415283c4144050064038090b01258100c002a845a0b03451009040602074240c00002c0015101e0081300805400b90003280c401c9a09682c0050200000b0094001079940e003c003680c000d0244c13a20b0409000150016013400741401000d1b60800c1c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 394769316 1250 394768066 394768069
    0x60e0102180409020d1101030b030a050606030c03060f070818160306061413050717010e0105010201061406090d0c12030e030d0816050304020a0b04080a0c0605090f0d150509030408010506 82
    0x345110303480c4d004141050441d00351361600814420910410704066031810300c03408070b4030104440607000780128014519844d0a004143c03920038140c1c003041c000d4001400380240f402254040e41d03081581c6040c0031030940e03920b1040c01192401d80c00c0000032072040000212010144012203001da0340030744010701a194854041220b500d1404071140d802a954203503030403208071a98811750b00142c072485d08050030741e5902c86180c1540c50a802040481600c280100081d6030244a445d005001359622015640001c0001412030301500b2a080e015800f2081030701c0400644101600103044002042c0c0642d600710b007401090703051540c1a4a000c1d03c14881030500e140d0044850b6031084e00000b00c1554401d0708a00201e03055000076000301c4e00310340800c801194661000c0d0151000d081c1d140020207501603581800e200720070b1107500c441309100080040089036240d1204d02040782c40e0503521009101c0c0c40e031924100707a6480c618242c3c005413030401032000005000c401002100c00c04d000038090b81c0c68800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 394770566 1250 394769316 394769321
    0xd1406010605090f041d03070b01060210050f16120c030209030106053304030507180c031a1009050a0303111203010e040b0c16080301050109170a060b060403060e01021804 75
    0x140329070b8003110031130100005140075000306c4001c282c8000d4a0030014a414522480e6401041049400041080051244903410440f03903054001c00302c000e100c41c1c00d020000000c0c02c1000b605410380504222007a911040c0a01d06000f020040c101d0b042003217114444006000350011000d00e4800d50038500d0024852a10b8101f4503214042d40050400d0451524900002a580680c128072018401d110010108005112032001490f036100c1c0e01119021800c9940116108103207405c042c90314002031400051400c0400607424002030341d64000c1c04415003419202c0e4a502d40c0901c0d030080d040700001c800c00d688400c10a00280c8000111010481f02041c0f0100c02c1c0024050b610188000d000002d01003100c4604068100700000160740c5401080360088501021010b025036108400100400803540d02216442c0101032410a00c10503080b8042c07071a448244000000d00711503200d510a0710103984802c100c0d402140d00400400c0319001d0002e07658040e4004452261107034403c460303030180c20700303003170 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 394771816 1250 394770566 394770577
    0x6050a0509040c260604030e0411031b0c0a061505040e070806040204180209180d050f070b150d03120b0d05032d040801290306041e020d1406010605 65
    0x10903004034460414542510080c007901c1d0030348111840b80a80c0013011400d0000d01c0c0102c0c001e603207100c103540c80341e024030082c1c0d9a08071112402e44c10420400140c030a8149035102c1c201e44503050390b035480c00c0545c01e151510a400c64051702e10fa2a08420b40308090340201c08130101c40c020384083c008400c0c08542d0725120b215030b101d170300c030300350810400a00185816400062803000e001d4000c0d10351300741a00031681c403003030071290305401c000d142d124504101800c00400c4d419810f58904640b078015864007030804c80c0a00480103120b85000790125035031405080003072803020006008103035141114203000f0b00c90444644038241644c80c010095105040c04044551600c2e000f100031460301003100c840e07000c104a2803650083c1c80e0030f010000350085179910700400003400101c0c008910748403000c3e09500e10300d00001150030316043d003601d81000b1f51408202641d000350004040c0d1001501c00c400161803150100c2c00940c0700c411900640c0401030b05e00321030511307007c06000706c0d02d00d0780e01c5903015550351081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 394773066 1250 394771816 394771823
    0x20f070303180e0c070c080f030405010c14032802010b150c0127050105060604050d080a030605090f010e06010807021b03070b0d0b0108130807030f031e06050a050904 73
    0x212091010a000706040074092800490408070540d59a0240001003401d64803c110700e040098818284500c94686001420b0214060040c1e240c064207400c3e524811031140505001249900c81c0502015010710100300313011805580e0355400e00240c05603000c01804070300100c0d088000d900510907105200b000c541d504060a880f0f003440d003c1172814030540003060f1000b460341d2a80c40031900e0740b82e24603640320607400d0340101da42c11018915010342913540c014602c42c0148410712042001d951102c0c100c01c00e841d001014295103114454048014080c2c507000240c12004e5401030180f0f4007130342c4a62a040f5820100c00380c19a80707800c4011119a00d0640c0e035071006901041900010001c03140800307084d4000202250f14035a560b0780582c5440c0c20111903994042d940b03200342c040079604196443c1e8401c0c4d400c00544050500c0b951003279481d0243e041c0140c00c02184a9007031802500039440107216031070036403003c1060a0360000039009807106018107030280c4d91801c0000b5880c2401041240221760 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 394774316 1250 394773066 394773073
    0x50408270102071202031009080c07091b0302070c090213210302060408093d0c150b0604120b010603180804120809090103050303150d031b08090618040507020f 70
    0x141c030004c41c1e4440301455060360716014207a4079400880c0944203001665210b50540c41c1c44038030280d01182003183e10303844070000d98223104400300c1b8140311000300f80030008141001a10340359142040d9000940940003803003031a1000414091404101c07003928121499900d1200c800c3c0e0550450a81c10941d050008001d40d10030000310f4001080031001d031020180151003041c482807002d8045c1105014001810701483c14241c030710004001042c8070510300c001a052040d200440c030f03565000390030784603810064800d80d28108003c0540c0c0740002c0310018110450580481c00305418514107a0800f84a4000030dc0c2c60540b0014551041107111400d554000342e910f81040e00e0031480e0718607207805540440300903100b08040b909a40e14962100c1c0078502071002540c4918010007203141d42c501d80f50849101f1606140d006001030783c420b90303c94003000081e4170140300b050f41e032400210500443d0b03039103588540c0c0429044004d003032568501d1031a42e4112024419030b1104e82080c0c1e280c421a1201c9603180e00b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 394775566 1250 394774316 394774319
    0x705280605030a0b0114120604110a030b041503050a03140f0705010209030f010513021203040306090803040c32130c0f030b040605060a0503130c060906020c180a0f06080105040827010207 82
    0x41e0f80c0150b80e02ca140035100ac01c60613031070400e0950542c406002d41c000b099035181d22a035507090620418421364000b0015413546811500e8042d81c800c0840c07401400c0010104803403030700c1814070041c0c0e080208030542240c0c903000d003454444d010750410b04000d0b01a20402903c250701d008140120350042801410204122000f9000e00c00c40901411045155110410000000a115128a102190081500d15128186031800030348004699208580c100c01052001e400c0c0c1400003c01d03414032094401584101884201244600c1c0100490144042c50020040d80c49174005011003c2000141c2d420811005140708000403140c10b4014030703420850902029a28070701a5004542042c0c3c400d0305846112819a9061300c000300316000080066040d007800c101c031640401518000140440e401d02d41080154034005400b031004000142c01d9403504c0100c21810420b502a034013400600000780031900e0107081400b816404683c0d00d800d15038042024071184081c610030801d6003001603004d820480d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 394776816 1250 394775566 394775587
    0x7050412121130040803070605040b0901090b150102011508010c0906080c040611120c01020417060906070e06040801050c0c12190309060b03060a061503020a020705280605030a0b0114 80
    0x1149034042403403c0c05403c110108441c64100054016244218008102c0d0f10f0946000c14803036030081c2c11056a0381c100051100051400c41c13120798090b01040e101d060340303003070a00102e014107890b01d03c81080085002d00810031703843c190864001111702c0d44628000d9681c403002100c50841c00c1752740301c400400074481401110b10440c40043c00c2e11480b4125030401581740d620346420f5010789940754041c0e500240070003c1d440c0d000f03050442c1b4400d8030090021784c5042d02c41c1d02d8461500030800c40401c2482174903180256201820399002c0c01c00031000700309600c4c0c50001c00305c03250b201c0c8021003494482c00c04e003000340303901007000c0381d050001e1034003106030003400b090040e00581a0804212041c0d03886003907100050301e040000c1c52050300400c10120b00540352444440011040880342410107004200c6600000d03000500c40e4101d07082940c6000c2d6001c4804026007080d010008030511148030140001000d50703000010b9801406030903000c01c50314141f07a0056030324102d0b9401d60f8968000034400c09039074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 394778066 1250 394776816 394776883
    0x1061401051e0f030c130608010b090405040816060f06050607021503100308070321020309031204020315010e181f09030e03061612090503030f070504121211 69
    0x10ba02aa051003410b10141e582c00c0d840740c1c1c01c11504540000d03800314079101040b081e00c0212000b40580e0a0158030755040c000c07070ba0114820381e4185402161a0008078040241c8001182c4001081110780703d015110b624003c800f82200300005044241040c2000c152460041d040307071030640d8004e0000d40c00300002078a1100a8100501201d006480c202e0f0000c0840c84920041500301d210380e46141070200206907005106001c001064402d80c418410005c840e000001200e45058400d00010b0746a6103074800079141441414004000b180d441d000026040400480c00780550707000d03006040e03680181d410803a030f00c01102600d5400720701c04c001c0b6413107078403144e500c2000482e0091600c0e120701900c00c00420704c0e0481c16104242103910000790f880c3c00c43d500c820305041d423035407071340007408019219185d5503500e020140000384200900b1300031a800300c0c02081118020181007510110401440c2801510007840c452000e0108110b46052840d1440100d03400c96408030502110b4400400410410036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 394779316 1250 394778066 394778107
    0xc05062403280c0b0703050406080f07020d0507240e0f030c15060609040507020c12010207020d0209070504030c03051005130f0816060513050c10020304031b0905090a0201020106140105 81
    0x3e00701491180802c2d440020310081030b4850207034844955491034560300500d4004028000300c60002d8078402d1020359540411a905201142d04d401616040107062840c441c0e5001e501a44a08200c2200c41d009440d4503041440b0507c10f4509640341d00c8594ae80c0117441c0c0c0724811001e442e58001c41c41980c0303c88030301a5030f241c00010240c2100e050603107000218007200c8040e2408800b40c0c0c02058105281d1400f034039001640d01ca0034000f94200b4841d540852048082400024403580f00c0c0c20005100510440654000310741100303070f242c0351550701e051250303d5410340c0300d824140c181020002031a1006000500c040c1c1caa0001c8800c3c0c040d1000d484401542e040000c0381c2c200565000b4400000c92040e00030350b030060b40800c3c0c004091000629181d480c0c01002c540003802a40c960b440d04151a0f0084269021290003440c6c107880078810303601140441417030f0341220720405e2404040c810b6110002500b00c0320a4800e03002003041d1030715103200d0451000865241d900003a01045000710701040b441d140e14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 394780566 1250 394779316 394779323
    0x1291605070f0b1c1413120509010c060b030f190c0603060b0a0c170409150609060210090203010b0907020c0906120309060d020405090910050f0f160c0506240328 71
    0x45c075941410f80c40509a0402e0b81c410710071985070320030303031091288000b42d20700c0c91111400c142e071620451000181c19694180300c05002caa5403140d035040300780c409000910110a504098480c0b80f00c40102d42544e111481d0415540b083c440340000c250280240f0403401070303c100300c0f240741c18031140d030b01c0491b400c40d102802212001c0029203040303101c0640030041c01c0517003000c03000890b00b400102001415110b10742e00240400030002801c212058000c80c50b08000040042c000c40c00e0340c01800030034054402107444c1c81d00a08010b003080000b540c041000780250100712154507458aa0300e0170000c41c00f040c525422010f070001c0140391002d2621b58010b200100751070310003506143d40c800c001030941030b00f2103100481303800407049501c445015102d4035920503520103c10b0003034241841080304814006042801b200c84001a002c0802c0c040d144001d12141d01204864492411851840d1607140000020038020641c050b05080742c41e000c11850005804007040852401e41700c0d280d42c5550303100d580f05a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 394781816 1250 394780566 394780571
    0xa050609070f0b0c0c040f0c1101230c0708190e01020106051c030c0210051e03150609041401080708011413020108061203070305070309080c030601291605070f0b1c 72
    0x81d417583c03110300856604070b10140d0300080725451074901810741c51a202c100c2885925002c42417040c00021411146451084480003480b42e64481001940740302d04031003d480c03a0808034a140542082e20419290003000c2c0e50b502400c14011001603003612441d00031301d030f40410000a16010b1122103091011854003900d0201080b4140c1d80101c1c01c1e200340c40d9084000250700003a40800c2020440d40548c00c07540501146156180034542081f04128402a19110303110004485a40c3c3da03c58100106039034000c20343c20b4407540d462103099921403403485034030b4865080018181800040564161242200b10707903c80c410211a8011550203000800241d032211841143c8401c1150070000f90180d0361190311010f42d12401401c0250010300c141d40182c1480e03112141c2c0340d00b142c4000c60581d04440000b507255800c807101201c11500009451a501039462001c15460810440403900c00346860050007aa80c83c7c6455a1040008080ca8025000d41d00300c00c108031122182442c002c10f0340c2e0b10040c00c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 394783066 1250 394781816 394781833
    0x606050111070e15180402090105010519140705030d0903020f07080c04050403021c080403090b0702030d030e01020903010c050d151a09150714060106032304140d020a050609070f0b0c 80
    0x80f044203028100d0f45030f04170300d441080214140500118007401090030894200b04034007108d4800581d200503610f0401240c0740c146039241080005035081140c1c0841940d0311000704e42d110400402100d0000d40c01481210078802c805100030551000742c0e12113101500000880d130b0280406400d024000714110b10580c500214000d1154552902010465950151030300305424020a045030300d03044003214880410040c801641c0c0000c807400710000350704021626000c0c081d40c0c50300a000e21005a0f405500b0109003d40382c40c2d001d0000c04d8400f202440820600905c1d80d00c20440140c10b01030408030080615100301e108880501078011800020821240f2000d50880c0c41c485402810040b1809085001c041005503000d00800d8090b00c2140341c10403403401440404010543c10b00d82400e11500c070030300032506000e1a03c10010301640d448003180c40245070b051000b50355500040301075800c0c0c0030b8034000c18210a00401d28100311107480e1414525541005441c507e2544111002c0001d840391404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 394784172 1106 394783066 394783069
    0x11040501030f06050301021602040e01020712080405100f020306040f050609060d05030708031602060a14040b0901022703010e06041502070c03080c0a0606050111070e15 74
    0x74045000000c0841c04002051a60442e42c0c25500011304040610b80c10301281c0101d9100340e800708107540a220900d4200d0103181001021200c1a0001e142c001d8854148607030064011000d5034010848010080221580a01e0002c00719402000304059072516201d8035450902c010003d00180c60100000740b80c0400042c090f501c500c032004004801e00c00304109981d00c2d0742e07212010582d1780c00c04d120b100b01c096448048040052150000068140407035000b451210a04001081d200c0e031641c1d0359040c00000006c0c50b40034190350910211038410250703954410f10161801001d0303079500c64a02410b0940d81038442c0002e40340e0000c0c0620000441d4520549450030030550010f072190100d180c10741140a455201500341d400118400c21405404205000e48503c0707013030200071841d9647c2c015104503000030a003101d03942141c40d0820140c40e480315010750201d9085510500100000d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 394604316 394784172 := by
  have h0 := BRFrame.cov_init 394604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 394604316 ≤ n) (h2 : n < 394784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
