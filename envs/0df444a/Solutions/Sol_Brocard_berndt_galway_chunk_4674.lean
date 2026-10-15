-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4674
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:22:27.572489+00:00
-- url     : https://prove2.me/submissions/a50164f9-65c8-42fe-825b-6183b291ffba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 840467625 ≤ n < 840647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 840468875 1250 840467625 840467669
    0x90601060f170112120f12020d02040306020406080f060a050a050d02130c0509041505030604140c1e031506060f0703030608070801020c0706021b0609061209100c0c08040e040804170303060406 84
    0x14421f4000e601900107a4421030180d1400c002c0c050b94000924250001600051813580082900c1c05030b00108145500390702c90301c041001a000c1807040b40c4d000003201c4010041454494125012603001410450122a040c480101142d19480407003010a402003600400c50401d441115030242105034454200345c28070f000a6501e01005200038550341144c042c070500031005204458040c01e01900c012602504581000500c3e440200202d000c2e1080791101942c040240010340d008407006403800f40780001e00303240c292495210000c15828952100000692000200050b800034840000010780310148007159600b880c0c0c01b82d0054003158889698015030301152101c0c3c500081f0200d6581e9a0f4454240104201307000f49140f5030003181424042105485000c80c3d924020300011008018090043c0f030280d4072603a030003030090303c0030300188014041c5410740d508403078019010717900c003e0401c1d03500c0003411141d441800b03e02d1842d420110a1112a0a007800303480003400d40403e98009000b0309010b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 840470125 1250 840468875 840468887
    0x1170f070510090305150a0b220b0a030209041a090703080307050a0306050613032108041205043b0610210e150f090601060f170112120f 60
    0x60a8032070b21204400c1d1a00d6400390200000035540181501c00400900510b01c0d041038045400d40901420311754400c1c02441c02c501030718405254040c41604001c1001160401004880c00e0580c000c0020000030025988811625100d6031159401c5d01c1041120040b0220f0504040c0040843d039001c0701081c0002042135090741d90010b0581303407154a800c081d20b401c401038804e603841150441400204025180881d10001040d20700a4078450b1003032800e5116682508158185a00040e14920114000a48112695500020519040d801d00c0d45481c408526107803900c8008105020741c000e2240000c03907506642c0b000c9090050188514a00070700800c2001d2078608a0310204150010300440702003210009207419601104d04212901d29000300e6a9a00342045500b100010500c00103000507004407110f42c41380f50460040c100f26441c00c1402d83d100704542010300184608075000f500300e83c861420582c0209800c181807044114039080000307040741d80e0b1079020700300507405030f540e0380c00c0790061 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 840471375 1250 840470125 840470129
    0x5030c101e1506031104030614090714060403080c0124030c05091302010c0311070b0d110403050d080a0b190504050702060402030c0d020d080a020f061003150b06070213020301170f07 80
    0x41030100c0d9845d041c090b0003104d4450703500000d2001d4546040d046400181c2461280b0070315121040700c3e00d017078580501001560a0038161503100c04104014000220b030840584041c82c03241001240f800111444109001440412022042d0105034100140084010444e00900302502c814140b42003c22605016180a034400f030306100d1250061400c152107000c2600700c12414000f607456443e281c0040326403541c04210414440c50505110349907a4000000306c808072a8010000c101c8288403001c192000701000b408079030000c0c3d5401e0b038410b541d15181131400c1141c250500e400607041c1090b0070041152000f500780b000b154025002c000042e10005081c0c200a80300300c4810701100642d2000410b510f004002c02098a9008035640181170303000104c01901208004c140d441c25660034101c0001c1c01708520028018030b054480d420300c00d03550b80c1d00510341080d0240c88140742c8492500841c4c217000d200d44030b030451a5400401080505828801406070715814806018034500f01d0b1040d9560352294 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 840472625 1250 840471375 840471377
    0x41e060906021009020d0f061b0e091807080703030302040302011106070c140102090402070b0402120d1e0302190c200f040506120a0b07020d0507150905030c101e1506 73
    0x1014901c0965a4081850f0310a950009035038002804907c1c18401500310000c07000000811b0b4940803274003c1c01641c00c544a181b010703200d00010703a02c0400145140d9201c3c42020002d0141802c0072a90040a100c250040d5001c1d480160752140345100040031600114990342880c0c101c902032095040c5d021025080060300319201003940314510200301d00a01c00c0001031a486413000406000700111000454032641c0204e4400e40780d201041c0c0220340322683c0d00d20180c00500569101805041a0b05c2441418400351400606210000d42e1409107103d40481c0b000219600020820420000b01030000e00814801c04806500c0928400714603c1c00200c0c182d28803503a21117002422580310302001c1c0860391070721001c1780c0d500c0c6030f107003809400360106403141001400384515941665000d0402c0b01e80265200c2e001c10103032401200728000500d1410000c9840780000c0016660002040100403c14030040d90001004850460307050b006a080665000015052074900d50f585c1c0481d44c40e20040b9046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 840473875 1250 840472625 840472631
    0x5030c06070824060405040606080406140c160615120606050f0102030904050c07080f0310051f0e01020f030d141825260d020105090c0f15041e0609060210 68
    0x4480010b2480d0013960041b903001381c0307031207000503026030b01c4002c0c030f40079a00a980402c10203410290754202c4180440d0b0b200c0003030a04004002040840c0300031286003a00481700029420643c2c20061029151a400300407101d40303407100c0c10184095880313640020102220030070907480e04000040d40761300400c0071440c401c558401c002040690300c003007147d4400364059441e0780e0b620860340c3c031941d42c3c5d0000d03900242952a41c140108d19400c116101c20b60b94500c941080b00603500c100821550003411110860443c051030203402d442c40000c00c054100400480c201151840060401c202c1040d8014002414600c5032202504d60110104000c0841e05550009903442c2045c1d0401401c06000c40c0e11070b18504d150030041100240c4160707070b025000100b050580300c051422030070480c00c2c0d800507a41e248103a045111820715034076180d501101c1c001c0e80035102081c088940301014400b0382059010441154111062000d502c404280c050094245803c1c4050843e00303200e0002d41c1e400c5c4c0f0b15680c1e90081e603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 840475125 1250 840473875 840473941
    0x810091103070308250218040206090d0503031f0b04060f11030c0d2d030c0c0614040b060a06020c090a14100905010f080a022b05030c060708 62
    0x4081039003404044800780850700308640d01c0c6131103541070f03010042c0c4500002c241c1040e60b00c080b00030050b043d8510b800400315a4001c0c24040070388140c5601030000c0b130b4041e40800ca8036502d6107421411000d07150083d4040c644074a042c019580e41503a4400049111106000050160003030710b40654040e5582e500c0c04103c6140c00c030005880341c111400b40b400a605c40441e10008484001980c40e1804040f45d9400c51030801c000086504020758011380015800100400c0084611a601860600e03c0d81e24104200340300c6c54542c00200e075190380e03450040c00341c00303420441841040c50200350005000d845400c8818604000203499030021106503105e401c00402050525846802401107086601a024100e0801d610640408207a920540700528103110000031030540202c41d50088071808006025080b80c1c035801c0203100c07041c900c6100302034001c0861090420000001d401040b0703110304c0c01159141e021803076152414000034401000c10140c1c0e01001001120f42c3c0910428000c0000d4000d0503038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 840476375 1250 840475125 840475133
    0x30905120a020a021309051608031c1d0601030c0515070b041703070302130b04050109060315080303180118030906050a02010f050702100e0d0c030507060f14070f020601081009 77
    0x3203e100d50103540000040100504900103600071702a09204004a07203a59184149107000d22050b4403904049400138010300102c0d0101c004c2e14001003090342000034682d0809400101000300d103001304083c50384802c0c01031040082c2484000042c2c0720485044110381024111400c0c20310803050002e03c14410710f000304082001550104006a020741c0302e0070348911302111700400075000300b40c2840520040764000101031000404603030a503501a510101d10504105003030380a07040010007030b402001c10403000a58004284042c3d80a0400d03c03010700d03204002e009250b400e440c8403400280d0300031800c510100019401070700d150304407034046c141151900b0010100303034010301a5954510311942024100b0008940c045480b134500d4880d00c40800000d030b080000f490b81d80d071510b604400480d02d1001c0000109010703e015000c49803281c0f00c0401d000031a0f80c040c03002e44a6400520f8800648001485612070300040c44100c1c001182c401012590324007009595180403280034005501d03582c02c1c0300d42c140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 840477625 1250 840476375 840476383
    0x40807030219030c0b1501021b061902010b01090f14120a050114010807170303070302090d08040308120901020309100e070f15020d09060f0e060904050403030e0706030905120a02 78
    0x500440da10786210901c507400e0240081d22001c02c03c0f261400800006411402500000306c56424103030300905100c117501212032600d040102019a000d40103020707820a0f03601c0d44014400e018483c1d0300115901402d20005170005da415003000481411860083c4001d1210940c840c030401400c84250218800f040150380c145086000c2c090065400c0c42e502c00c4140d46041c280301d04803081c04045924059032443e20007201075840d42481495002000841c880030b101341c0203043e10b40001003c4002141d420b599484a0b580940c5c412280c91601040181861400445043d4886101d0f0025491841c040f02c0b07c645542c5076916104e00c0c50b58588081c000c0140810104001e0040d0100038072449890f103000d0b05008454030340510042c030039140c103030464900c125081001c9501c075444100c1120110881501c1c903050709541680c02501c20b0000d010319566500486d8001c84c000c1d100041e0007038281c0986030506005403c25014182004a02c20004d080011180821040fa000d070507118018880100c1c20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 840478875 1250 840477625 840477643
    0x315110904091b091503021e10030c03050c0c10110d020a0903060506040603120f12020f0306180108030901120b030102070311060a05070e130e070821040308030408070302 75
    0x51808841504009020f041d03072161009107681801c04030366906203101502d0740c1d070f03c00c03044120441d181040107041c038501d42d0142086074000f0103980f086000210700385841c02a030030702c0081e49414040c60000e400d48506d070b42221000300301500c1c00b008140b0940d5a5040300e01142503880e5100c62080d4202110019620000440381c2e095590305801e0710000c1c4075a40500050715640d10b042e000c50280e251522600d0112a130000c030540683d686040141c50f43e02060441005000200b450a00e103a03d880c070007044446c85141a45860741045000c1c4402c144241140c0030080700c02c01d0052200140000580b0384000003480d08600014107508844083d01000354059015030020445004040e044600101417181c2c00d4219103055641c2d90300c9106036081521480040341d0101d050008504014181c2c0f001306032080b4000c500103001182983c500840c56000d109150004c071840c07a10450f00340c4424410301c001c2c0c03011070b00345802c40e101c011303492001820040035040c000a0580400d4024000900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 840480125 1250 840478875 840478879
    0x90a1709090420060f09011d240705060117060703060b03011406121005131b08130f0803060109060801050f21010203070513080d0f1b0b1317030103151109 68
    0x18403402c40b01c0080100e81c0081c600107002c0790048d1701484200448018220100e4001840c0c1c0098062001200480c0b24190100a0345001c0c20495500860820044076008003240c554054001a05c1c422030380c00c1c0000542070004050174032004010350602c80c41274030b0545046121803a02c8054070000156284101b02c80c0740c02c0300c400c000801a9080300c2c01c82c400704913281502c94416441784003010a003151940140658400040c680d51307985940f15140480d4095400c52081c0c3c0c0a0995448402e0401c02e500b008843c1030200204001c43c2c3c1d644000d00b1402030044c3d00303040d2140d504003400a002204180c1006001c2d4030301c01c0e1038804070008541c00c581200c0f0890700856a0381040c5c90010b0080c4e00c02079500405003140ba40014000390001742d001e20001c401e55450506004038a0b0440f100010b8a071100e82e00d004551045010900070104940904a103000301200614140ba1035281208a40046840c014082c0010000702d481c4815a00b59440300300d178005200c0381c0100c00302c01a4022013210b16 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 840481375 1250 840480125 840480127
    0x8180703021f111c0c060b06030a0b1003020c0604080a0306150c0204152909220c2a0507091109090606040b1602030a050303090a170909042006 63
    0x12041240d500ea04070606150f076880b0340c0d44070850881c0c1e507554074000304034002c80083c01d501070510920458a44c00703c03a2050b04d0100c3c6c104201344c001a059002503036100303221642c0d2820a0b84502d040300d070803080000d95040550800b11030040c0207454400040000c2e00001c000681944000c0c829030108003c0e001841d07240400d00c170041d100624042c03100070100e004901d420804809006060f00d440c00f200c6040308185000003850ba85a00294001c84400016060074082032409598848080580705550165045081c06484c05c48050741c001d02203020612601e00034580030700c040e02c0030703462403080c01c5c04c50b171000e44074240b900b10310b4110903038424400703185060088482d0903181c0004000c428030844100f419611440300b0000540300b140b10780d8004400070043d03120001d9007100b180490b00e0008082c0c48480213581c4800703040d0b44c03080720010581c0c2c05c5070030490100040c2c50780c2c0c0c0c18400c5201c4506c0b410003006d400070456040018001a10ba951440300c02006030f0315035185441d501c007000d0825 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 840482625 1250 840481375 840481399
    0x60f0d020d06091b030c050402030c0f0c21090f0d0f02010810030209040b0405100501060818010f022206021b0111011803030501170c18060102070902070515060d030818070302 77
    0x1130003a015640022070b04280a02d40c0024546007a0007900d000f008c50304040f81c03812020290340d048990141141301060f020f0340320301e1501071100050340c2c2c0411007422040b990b81e00310b090420a14007800b4201612450b2000c080e1000700301400030600140d1790a09081c00c003900c40c201505200211584001c0d484007500c41003000708503100b10058080d52280c01110342d040007031040c1000380c0c1c1c0c003401040d000032010030025030002405080001c0700114a00006540d64081200c0002d03a4007000b00340010000d2024029800e102c02612200103010703c0c4041c048800923081442070102e110001207041048158a070126500294448401c4010051002480c860b0600c1d024010b03000911a03052180d0001c1c3e2041600800801c3c094070340710005000208400900c18080c40da0036024050604510401c4001f00310f02e105403000b40300c0319015000812101c0061907030500c06510040441d4090800840203000182e00f0440c0c00c1e42264114158581400f152a010341ca000d04507030020b5480203070400342e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 840483875 1250 840482625 840482663
    0x303010b04060f110a020f0103020c01020d050103113304080a050f060a060b04180e07090605310e010216030504030b10030804030b07180602010f05060f0d020d0609 72
    0x14400c650b45a00d42100d0055683c02c20340d05510b2020307482c3d0007030704844c0900d4010f1500020768505030105040044c1440c0e60011910b003241c100e44640070500d556000180184881c4252042e5040d41c201d030301c0c25880d050880703040c400031110003541a00582d0b1000c000d0143e0f8601060b00d014244850480e00b01c1162410441e41d034051110072898903000da240825081051402600c084d1411205030a00d010b2802c08508180042d000803011016030f900d6908942500070b10501380186003120b00031400904090400c0002c2d4400212010340300503000489860921804207080c0f0105611000a403c040b46401180a40300e140750785202a0240400c03a410950058041c02c10341c4c1c09110b2600c07080e035420219030303010a45404040c1c0014400d000420015115a01c4d0340d521202920340304414107070355a800e0288111a4100d480036175185d088a82012400c4d00c9210307840343c0200e40c01007403030501e1000304403050006940030340600440c0340c10800780500c07500712028940d0700000c0e4542010340c04003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 840485125 1250 840483875 840483877
    0x12020a0e09011e06050d150f0608010605120105060a0c08040b0c0c03010b1807031107030302030702010b01020d1233030311010c120b01020c09041115250804080303010b 74
    0x2a5a07442850504004280d100031810342c0e650446034205a12000c0d03041450950f1705070000d10b554900d00da2901482500c40c0e54030078401008200d00d0000c131040c941060009000c15005070020000c0240500100d00c409002100c12411640e06442641ea01c01c4d02c80800c40d6040100d0700e0203454428006400560028500002c20034031401400762040b0342c1d50802010300340c58100c0e16895024000c43d0292401c0b039000d40001d60418142c0c1000102d5940319040c01d580c0ba0000201035000c240c1c040200302c10640c082c00386501c1c0354400d10140481901c00c640207410103142604848440341c0c2c0d0450b00340c0c54288a5421780d40c0300781c8030a542c0980001c000955071405c0190004a00269442c0c00d400c10400050066280d042007030b0700c2d0b44548080b080049030013000048240c50440c0301d01c1d0f148500c40d071034407003401c1e0080b40102ca10182081c60720043c402d441c150000300c0540390340100000b00c0c8041820180070450010004d0302c0b510016141882d5045005540101c401c0d0f0100000000d00c1c0c8545030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 840486375 1250 840485125 840485147
    0xb0c0c1f06080f120306030a0c08030304021c03090e181e010e0703200105120703091e03020312060d12080a0b010507080a0806040e15040212120f0a12020a 68
    0x402881941e0301d4404140d110301204981000740d501c8101289110071149010317540c800409812102c1c20300150320342800d01c6090360300c0b07203416410000600065003499402000d04c0701215444400401032560300403ca11003500c140500c00c0580380128a0f80071519150f00e001842d480120b500b034110440d5407011307076842603644004540c608600404038040c081044421aa004045805101d0001e030303403989036110040c0345a040150030024030031211005c040141c015445a58009102071451808101e0812104609a155442250328600003070740041101e240d6826110144c2c90341d01e841c40814500482210700030008040080c150340c1c4664403203140c82c403e04a04505001e100d8040d40155040d03c555000076001c28030400c040031646002c0d4409a40000002c0c0c00011100c5000103030f141000036110380c001405000e171051005500c0c10074042010300010b100a05402c1000303e081040b213100d504040c141d400030110700401c00c0e60103488088071000390b0400a41d07860482c2140203040741104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 840487625 1250 840486375 840486433
    0x20301150807051011030f0a120f0504170414190b03090607090b0708090103020c12030c07031d031905030702090708010611010c0f1b12030605031009020d0b0c0c 71
    0x10f2130044814034480c2c2a50580c50704044051403070710400b00c180c000164030401400741800003c4555401d940c4480c8036104030f0000c3e01c0300c0080c060900749001300110361400501203000c2d005000521000d203d0780440356003860f04540307903214041c8110015100380c60703039031000005003804010043c1d00d08001c21030328850205607640d000081e440e0260a81c2c2c5000d48003010b0b02d401000d001c4100c003940681e000742402c07003202040340c181404e08001c0d40d001d0b5100f2a0041c0008401103448010075401c4a0f00410340340c1c6850704000c050700001e020035581d142c010a0144d601103040d00307510900006004071543c0c960050030f140c0091410b0f180242c0208000e10406000442d191440d104108043c800d108060302d05a807203554941c103141c0e0486200c0c40c0c081c1194210703102c0302c00910000e04001e002d14401e50031030f10086905440c01c02007500703002010800031442401c0c0b041d1a00183d45a0350300486040d88584807050f01e840c1d03006020b07907030b000344050700030703903101d0701030294100c0144088102e507810003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 840488875 1250 840487625 840487639
    0x303090c011704170307110d1e030b0d0b04030c0f0305030106090803090d0803100810050604050105120a06021804050403210207030905040917070b061e1c02030115080705 75
    0x4981580c60700000300c4014095484240c800c444c402e84180003036030010058649104c0d082180000d850500c210b2100d10b8001c10820f000300d04200c1040317054103018100c18281007095421201c04501000c02100b8003c0150070750700b000804040c000c1c1980d00d4400e070040b5800e41d11400501c0c016085610a004001c04580c005d180040c440100104a500044002d04110114411a030312070307126810240440c00d607070b444800e0215510804101420040d501003102140a050200030300c400c0b1503040e080103014400801154042d0800059508120b03030748a54012f903584102e0800e800c1840285490507403180c02c0c00103000c10315900050900301461032200324200d840c0014214001c070b00c05c0341001008155032003070402c40c1e8581a0700004249009182c4502000d440700c00c26070280c4d000c4e060407a490b00480e0144007540c1883e40d18031603c281e45618143c8400b00d031304c000400101c0340d49103515006000702e45140841d00c0070342003c1c00840300000030a02e4180c4500442d910b4500d540106030003106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 840490125 1250 840488875 840488897
    0x1404090212010e160c060e120415020c032a1f08090331050d080a020705010f0c061a09070203071403040608040212070b0d020403110a061d0a080303090c01 68
    0x1c558a01a4011104600350400b0a0341132802a03624160307102c02035550326613448200305a100c1c10b10980a00a1100c11005d44e29400c0030040d040e01041c04002c40110342c862100c00b00e65840001d0b6a0790300d24884d1080481c54100158405105840100050f41010100850790050703c031480c403d002080e074685a94a40e96203241d88596640541d80207004541c00701101e543c050b003807030406c403c2e110111003080c80703480d80c445000c100040c0f0940c008032030030f100001d624000d6640c18802030000c0c081c01d20f4101c3c45245203d0307009000250100740941003035030725030852410000c05243c00c401404041c05040c43c0785410f81d006503c0740c221b0003050300e50022240c22241e041c0d4000c02100c01303070303075550700c5041050301c03150240f0810000f45250502c00344104207020130720b401c0c8940503050482d0f4216015035a181580707070a014514000f141c080c05002001000e000b003541100d00c120140401008080031003900304001001405158044200b80c0000820f020b110a004100201070072002e8840f140300301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 840491375 1250 840490125 840490139
    0xc060c030c0e060921060421081b07021203040f051909110c0102072004140106031505060309010b0f0913060207060603050d0e041a011b03140409021201 67
    0x4041d5040030700000c0281209440c2807a010300903021100010703104100340a001c881a24160000503440104d80d8417010800081142206104d0b1012405262140342034405900207803000c100a0202c1d42150204203490800305000c80c241c9050580040503400e109079500310040c2ca9601a0062000518154502064030304081600c144807105101d401d5666600d4503800100400400c58980d400f40c0c4100500104282b09001601005006854604916400100700da0707402c0521702d2114002d0b42450700f1003001140c0d41203628115555810086108812805035043c4090386411181e40120040141f05240c81c056200d950259070507076881d240c41641034204424001e00311450070010b00c20f00100c00c000740686e0040d103881c81c41004007080d4543c80341d50712801d05494014050004004109220741da10705030041da1030001c0c001c1610841001d00e080001c00485107111080200c10201d05078604040c4176190f20032815811441030b645803500c60540c3d00180d40162820310400e20f245c00045100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 840492625 1250 840491375 840491381
    0x409321009030e0907170103110a090b1305040c0801060b2505030a03020f1606021c0506030d180b0a020a03031a06070f0c03020a09091b030203060117010e0a030c060c03 74
    0x35500b40c1c4030412512011020807641c030b00018030130380406c0040c005204003e8803514205020b50302c259030070724410700158148440c8511f11b5012750f01007820011a05a940c90340b88103000481001c3d01c020405503100e05001d0000582030703000900039842c0901c0080d4011900b009888901381c001c00010003c2c40350342c07146112200f40fa1028005804c1007041050700f40c0030b0b9009013510812a1202800e00d2480c1881c0206c98100e4082990340302e800149a000315030202da8040c0101005130001c00c568104080401d41d240100c10701581400403084184e01c240381d102c0c8408000701441007505a603100d02d410000e403100011442180070900f0070307030032104080310280500750034440a0849030a040b8240c4449402810350701060b140b20010344004009070311036180d0403014041854010a80d040c6510b84001d244118601c40110708014810610044c1c1d00400c0241c11600c0c407a510401d00e000c40d01070140103200612080030b0910855000b070301016000090f000181e0701801007006007444614042d015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 840493875 1250 840492625 840492641
    0x5030a180b0c07061d030312041208010f0515190315060503041a0c070c0b03100504060b03071107170a02010927020a050d050f04050105060604120204093210 69
    0x800c1e00b1619013403180364807a45500d2070f40f64000d0072003042050b81202107400d5522007146076170b81038045000c010a00072401c103454604031482c504107803e0742c541040c0c140700c0b64041c040c0a224004135480300c040c4141c04020380e8220405858480c01624000201074000c0010311181c0001c03140076040064014001c60640344030f150090000c01204021081d02030240741d0051800c00c5680f01880514042400a8940c1001c3e0034040200ca55900b0300301c2c00080b06500b0b070360149110704e05201e8140000b4034040c003030303940041081c03c20481c0002d6a50140d810800135820510003a0143c2805081401c00058001d1900d4001e88454000c1c80d00c801c40c3d8030801d0082c0140700c940f85a0102d03155050740392540142420350091600c1810011400e5001d429101d054507a1020039030001c2c10301082c003000780708a507000b80c3c080703445520b81454000c8480341c080301c81d02d011744a907550301c41020902c455802001d05600001d444000c940e07050420f080c0b00b10410400c900f05078400c00c54031852440d058801c14131 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 840495125 1250 840493875 840493897
    0x90b030f12040608181c030e1f0911120d080a0b030a02120102041703041707150c02040603020405070f0e090c070605041109070f08060603010f1206060305030a180b 72
    0x202d8681429001d0300c08803005400e12004100d0710313002c034025080a100b51042d0f072a820800c484440a82070340101650155400007085800003606607040c40b083c1a44188403c00c08000400c2c084440c0c24041018400900c04070b8101080740001c0303008240205807a11031104d10b03103811800b51030381e040e190200c5289448994043c1d00a0502d10050302d0f19a419011380156840090b142680307510000c00c1c0d0100b100040c107999800407405001155440c0040a9201c941400030404907181081240060200d00d030200140414036102805640f00c40e0401c901564014000388200e081440000344961806148100020078000d404201441e16a9200c1d000342004000030f410300b0780680300c0c0c000074200a04100d40783d94503005650000d450382c1c07215501c05e100540701c8e40014015118003501811005100c5481003e0420051051074059103590b0140c6c0d115200201c403001c80d914100c0300510b0f1031b80000d42144004a2100e441d01e07070007054140c0514480d03108a2400c0c3e034550b40c50b0a00d000c2c0f40c10481c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 840496375 1250 840495125 840495127
    0xa27150e0114031006090b0f03340905012714061003061205030c070b030f010b0901030b040f0518010204150503060a21120e13020901090b0301090b030f12 68
    0x11075410b02c01291501c0ca10024191804083c000c5076600c1196501d034088200c598407030b00e028201d882d154a0682d44444141e01824020b00d035000801d0085a01c2c01100900c20b00121035480c1d60703c10709143d0000340c940c00d03404204a5856400d00020f0501301003200801840100035a41e50018901a08404840354011040c641c0c60785001c00c85511110f01014080542d12035001a60b164940040c00440c2c4c0a4405036540b038560103801810008103810014800d17208205000190034150390690464030603a101035220703442040124040c15500300e140303034880d0400549c80044849030340010701900e9a0311424071001c0114600ba401e0340a035104002a00701c400405c203021a00510040da841000101038101080d182c241d815030710a01c01001d5011920412019810400c002d80345242161903070800a0540c211240042c0000301500fa030b0080f090340228141006034090700c0d4040191040303a0689484e903031500440f078024004604110700c80d1189104510307043e0004070b800d50401d01035a140f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 840497625 1250 840496375 840496379
    0x3020c060106050a1107150f080403020606100c0b0a050601020705030106050d08030421020f0d08060310090318061110060302090c0306031e06160503240a27150e01 72
    0xda84541025140b4070610541c6a00b800d01d4070307420300c08400039040581800300a60b404090040c08c0da1164041c1000b0320026001348400702c3c1c1c001a0240d4400400c4860121940703548200301d42c142004100103142ca4070307103810700c40400c00c0b81c0c0102d8403483e8281e080310719840c1d5840c10142a18a07078070445821030008044000440c4421f001158414003c540391508444074804003229045a8550040180c20240b01c183c8400410700801e4054081c602e0030141c0c46c100f20300002e46550000001608182d542e00c0720300200350045846560029038020380602c0a5540e42010306190466914038915005960601110a110f4425a0156500540503030229581c6004e82d051a80c03014101d076034540301d084038202c4061000c204a1200c028900701a0050341030688210740040144040038003449020310070030108004800c01014000345000c506d00b5070260782c4001c501010a19004000949516081441d02c0b074000c031229080c041609000300306080f03204441da100451f490058000c41d29034a001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 840498875 1250 840497625 840497627
    0xd05042102060f0403060605030105191d1608010e010216020618090a0204091b050d091719090806040c060c030e0904060516030203040f022206080114060103020c060106 74
    0x240300c2101608010200110034030740019a50350015075000285a5001400740208a103600903d001041c1c1500240903504108101e5250036110041d10f40b51a5a15008456694804d61880e440e007a200000e4031101d51540070041208032840c01814900c1d824540c1c0d14221010500c00ca801181e41c140c07881160b40071a42c20800d0303541c4020400d620307080313540c4490710032070b540e002005004805468006079038601d41150403003660440b683c400c0003440c80400030040d1769000303411660760402c450400640c01d5032a00e001000c40c101c10344074000321600424030811707a1144201c4114803404549400c40c10581d2400c07425542d10046500500354100100300b000007030b0140d41000800c034824105031841c42c1500c0d001c40c125a0b8101d805503070a40d203030310502602042c01104d03981ca403141d80c6029071540c44c05c1d0725101a84042c03c50b0083c02074900d000e500300d24494650750544031204900c0240082552012428060054500d01800c110100030210b8000c3d8068821100c0c0a0ba40d480a400180e00c1c01c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 840500125 1250 840498875 840498899
    0x15050708071112030a27050f0a0e0a0f0f02091005030a02040e0430050a0f1205160806010c111002010b0306090604060b0907080f0a020f0409150b0c0a150b040c0c030807020d0504 78
    0xf45a070800f0f0b10209c045140b203001030340544602091140001c0c49002c40c00c00c101654034005548188038170400c40307a80903031509046036481891a041183d92500ca000c2e40c10020710850340910314225642c814041080540c00d9403201c595001c03040102c9019100d41100340031a103640c0300e180400c10070000c141080780100c0d119217910b08541820140c0080105090b02518412101e007031454101c05062940340340c103c1405030704401c2c2031800c0c580502e056a80c10402c0c4403c1c0300030341d120f92010700e508001c40c0c5c400d40255240e50b0f00035046d204603061000182d40d98138015102203c00383d0500c2c1020b0103c1c242200540d00c42e54042d40c54042c140c45a10317840e0400032020700030000c0e180d003c11401c038000e49540001c0c030007070424200005000740c5210000640c262075800c54440e0782000c22915080b650001842824940c11040801071825000d40320390040030340509460300706044c481e200082980003c4c01220a50180e01c07501034036919808201d841e4103a805069001c1401440240090307410340c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 840501375 1250 840500125 840500149
    0x506121b160b0603070e0903070510020301120609050109231018020409032304060915020a1515090e010506030d02100c05090301050c1315050708071112030a2705 71
    0x80e080e0b954040c0c5030386d018810b500084840032510b500005d00c65081060400030030080420940e011402c65040070f0940340250b40e00000070308569220011b00c2d051107803c1d484004450351100c0d800010b890044c4401616100901c03e40c243c6010341109442410750380d000d2100f0f03e024038086201907089686c200801041007000076801c200001030402d0f00101103c4180740403006d08400f80e9280c51401200500d0180250400e0f094034807510780091041e84c001641513280d5501407081c0039182100b94404005141c2c026994502c1c01c1c0e2070b03070001031142c050360240c8108460310780280b00942e248020706a440c00b080c0c4007000140d014859071680076a40e6804500c0d1900745250441c0303401303020381c0041c1c04e407102540c40243c20a0000790100c0c40c8255100b10400a20034145400c150403e6000060031600500070b01a020f04d000040b60420080e0f01c80e01c44156860042035200c443c032041c441540c0e6070700000042030120b00000740409001801010304c4c0300c0e035010011603c41c40c509000a1041310b81d404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 840502625 1250 840501375 840501379
    0x411060d0b0a1403010605010306050f21100209120105040314130306020c0709060f080303040b150303220501030614061806040e070806100f0f090506121b160b06 71
    0x2441200d04542d166101c2030001e1895580d881181200b000030503085655607408181414903007481040039031951101c0d09904202110180750590710300c0381040c41c058240f9264401c9009083c02c9508003001980982400b100607190150440d0170080d072242203410658000d030108603000b5295150000b0070000b4104141c036a04018900741e62940c1b06421f9030459a100000f0360013446050002007080d22800d03008000040307400210303034a030007170f45500ca11019101a00321030610b00003e0700303d0721440c1d03208040316001d01101c3c3e4035041103c020003000d52054104001c20900c02d400038042d803107402030006540c429091150b400c4054000c0040c0c90f0f1021903d0102003050101c2c1803241c3c1c0c0e17400060401400b481c1e00740c1819103001040203289520051280c0e1054601c2060a03585d0341e8001400b450720305441c28000c210640044c807ea885484a6021a5000301c0010760410300b0041d44055500540c2e4040740600030541049034481640a44c1a016500c805255103040101e1a44103405801140c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 840503875 1250 840502625 840502631
    0x49052704020f030f0f04080d0e07030b010801020304060b040c021002090307030204110a021911091008010c0e010207050d080a051e04240e0a05010f020f1020030411060d 74
    0x2590085400d036048418414030100010040052030034072510000c0c1e020403c03035503005140c501907441e13804a0080100714600d403680c40c0c0c41e040d08241c041080e5800b5540041008038030f580d4550010b8040d40c0111001c03071700142000c505034583d0409004407483c02100f5009481440481441d80f000cd4010400190323151050b144008056101da118041005042e1006607984450114006e1324000d54007900d0b4005401d00d681c0c600104903070028444100c401100d0180d00c50b02c405092188001181d0041c4105500e0030803040341e0241c2010403410455000e0302558102e907070703a000304103134558420409881b40508204810b4468400c00c02070444440000d07000320582d005000c00305150b046900301651071a004480b08507081c841c0303603189040345401d2030401d0100203024003003500c0034841c2c4940b5051240c19010703280000d00a00509520310040001c031800b015220001070040c20303446504120f4554204480b10380c5c10714a40440e841039070401032102040c208002409071562020401c1c80710256 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 840505125 1250 840503875 840503947
    0xb031f0911061303020a0b0403080d0b0102210a020114190b0a0f0806070305010e0615030a0e011b350712020a09051e010c12024905 58
    0x5035880c09040840200c0c0d03295210f16055206100d4131a02a4100243c001c0042c401000020300c603204444000e440480085000340c2c405006038034000c0403514548410154040b4082c1802c0d03210081c1582d540b90740d000f403000340301c00c4180c1b00700100d082e034440c03003110b8520094020007541504218441d9401030403003d1030f00c2e9501c1c1481c40007503058109100c0d82d0001c009010143ea49805040d003d030004444154041c01c2c080c1c0080e01c0b210b070044c0110354040c1e0120010300d01d0401980507514100c8000001c1c044415020418000310301c400c8090800b003081d40380e00c41000141d28a40071000e40803a080d10395103428502501c0703140503000f04042e040240401c155603400c10075001a243e46c00ca99114400210b080c1420004001c41c841d032201c10100c03402c2c0d01c4000c2ea80c4d02115000200b6040240c0d00241c1c6030040302242440fa0a203131040b2040c504460020100054000c04404e040380d10001ba55a84d240b0140880c041c00c4140d044400114248804e00050b039980919407500d0350320b000d00c01d64a0f1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 840506375 1250 840505125 840505129
    0xd1202120408010510090501060c0b07020705060f0d0e0604081204080403080c0105090714030330040b0103050c010c1a0a0f0e0304062307140106030507180b031f0911 73
    0x94410780010035240d4450085c4060800000c41001c040c02225100340469030400000601a541c02600030b00f00780104070100f00424000c1c40510042c3c14040e1403030313a580c81e000e8400310241c3e100500000000c1d14001c0e803000b9030307000807031182c0c02079034802e281515220100382040784c10364015005607a034000402c03000000a01c2d2100518906c407a1100116031031601c01c100500f00308440d4000002c5510b8503540d4003076983c020007164a07503031101514801840340101102c20440c0e0311343c911511616424180410f2224a01005041783e1103241207509140c40300b401100c80c50000c0000418090020140034012001c00c0e10349907002060359000140e00a00d2a88101580c3d074025141011303420015042c42096070041151400e85462043d9998000409440305000c1c4100c54001d4410160041c59581c0d521082d084000210340007012501c00301d80307807448215903110000d200c800c4149480c040c901903044c042002202d010700c50044d500242400308420015080c5c0380001c6030407540e0005c0e4040c0913 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 840507625 1250 840506375 840506377
    0x31116270212070201050603070f1a1c1e0614010804110915011202030f06010e03190305250b15130501030b0412090f030807060912030f18020d120212 66
    0x1916107281c0302c0341600341840e02a00b1220060049070182c0c019242c240b1545280812101c1181d445411080c084030540c5034642250003190b0b104507091007a00e1100005040036000188154541c0d030b21000c00f070703400d28503990440b02c49128054030410b031015411415802905075542c0140078a03040701800c50078100164429404841e01e50342000030f4890300c0a00d5912001c03079100805900401c600d9030034150f244102d8000002c00c2c880c100004021006216282400302e5589980c1544a04035036045520380900b0035080040da480140303546040c010080011300155491160300300001103441d859000c0c07070b00c030b885001d12501904249610025400c0c05481d01c1a580203600504045030076041c589849458000841103030780c2004120780b028081c051a0154000c11a6485180345544204914114000d04004400130300b10751800c1c004158499095004801c8084400780d041040800a0000c0d40c42d0985078034003c4d401103d440e9005000a104502c40a40c030302741e40c011940e407214031440301012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 840508875 1250 840507625 840507637
    0x60c03120f1803030b040908030604050702070314030405010206070528030213061106090c1507021503010e0a0f0c050406030f0b0301050408070c050d020f010507060e03040807030311162702 83
    0x401c03640d80e056800b410b601d441805d00208045034188003d21141c1c568032060b000161040703128a9440002ca11118000c0004100669001c0000960100c1da0410b1540301d8101b8403a090143c043d05000500d007501c10790444845901c1d80181e4400480718400b14074030402100528018540d08010414042c925101010020601030752035540780c04131640781f141007a901610741d920315031080c9143c0b829542c1c0c074801c0d8200c0760b01c4402c000381c41c1c95a500002e008810762004d1940942400000030400400b01c2c0d4420344201405c3d036082c090103265042103422140f0000032407001031001d0006000d018441d0b0004003403440e000e00f0204051300d2000019007101c0c0e05071021103c9a0f0000ba44004210810007c20000c040440d1214034481150300801c0140c0408981d01c0c0c10020002400c03c1004001c0e80500680140c0f04101c07a100d540f2840007641e5401540001c0c0c010030342111445085000005850407100d041c0d0031a0705901e03150103c5c5919450840d4592010540e807071070080201c08003440a045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 840510125 1250 840508875 840508901
    0xa02011104121a040b010b0c0c0406171c021f0e030d050f0903030402010203041401050d090c0f0f051003091a04030806100e0d15090212010f060f060c03120f 69
    0x72401002e180c4030940615903d40c0301400b00742401080041032180c5c1403541100d040204269840780300085980c20001031003c078070360240c80c210003c03c14a440c00c03114543c0c1c0b02541c0445620b03c03012000e03001951042500c030300040e4418034110804c89014101e0060003d02c01a0108803541c07001c0c5041c0c150380044040b6a1041d1385c5030100690f42081c41d414036040500d000246245041940000392640303d030f0700411381803100c243c203003c0f903992107003040751102c1e4140042085800b5103858103038030340101d47c481c030000c2c02d184110100d112001d643c0010102d9600400c001c2d602d51f040c0d10281c018000c0d1110580d9610084000d22041500140c00030b44298030070b58441200d40b810341c08000b80826250365070f10401c910046000e0309901d03030705100c202068001009001300f041c80040702c8081c0c800000c00a401c0444000070103096070054001a0b100c91038007800740215502c95681d010071840a220340d20018103031404500100f07000e60310008000d0f030880c002103104036044440000f41d89001040d09 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 840511375 1250 840510125 840510149
    0xf020f010e010c03180b0f060607060212040201140a0c0b0405030708041e2102091911120f0705120c0412050d0f020c060702092a0703081012080a02011104 68
    0xd03a41541c94450a4589040705079115901c2e45c00d81c660841d4050f0080c800020801c921022855136079401c0d065900141e03000d6002d5584005100c0a051004020758003203000c0741c6e65111050b6540581402d4071440e0100341c1d9000c03402d030310a0310340029502015205031094041046000c001c100b8801c0148043d003c046100d010070082e10344181115a90f0f94403103030813821a01c0091840380740c5116001d800a404451481c0760b525520054140004000045214103261201094803111464080c2c0400c4605500c20020366480080034803850380d08aa2010014200f0022a00c0303d90301525001d8024002c0401942400d807503a803240041d41040000751000d0703202c495030590256010441080056035440039206030040c1c140419240d0141d800b000380320b8100800007504848603206070410025008081c1e00f03d40085a411516903800084280d000804a4001511095120300a0ba0484544100c400d011141a1b251500ca40e08052048000c65494921442c2c1050540d005231007e40600e901c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 840512625 1250 840511375 840511391
    0xe030904023f06030a120509040f020a09090b06030c070b04030c050607050d150e0a0b010e10090305070b0901020604030e190e070f1e050a1209060506040606020a050c010f020f010e01 80
    0x10b5581d5500041c03003140310754022803600c0d0000318030b007401250049403824840e445508440c0000d010344084040001010b10102c0c90310f9180e98030001c4c0c2c00448804c29000c108150859050040521040b00e800d80c0042040200b400051100204240c0c0a4001e1402c0740390381495a4440e410100d0945d201b0000a4003c21902c52004003885400200e40c0d0018100c6840c9140c40d444140440d0001c11000740b0325500c0050210782d9000b20b0403655201c10051540320000504080902050042d000c2a01c880c81814808103902090204a903a0390805030000c08450782c4595040325002e46d000e40c06600002c00101c845605014080544090181c0c00c10040c2d10346001c403401040321141d203103808100f1400c00811004034481040d0303000d01d0303001da10b0460380e104405001034505500c2c0e00ca0307076170806113090006c40c24006594000c0307001d10011a000c0c03001d00c0d80e03240c04aa40c2c070384002c1e000d04641c100030544210381d8000c40d40710100d2000c0d4010f88004140c42c541e0716084070005c110f0b0800d035075102c441e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 840513875 1250 840512625 840512737
    0x30f0210020606180907180905011104030b0105060706060e090105161718010605060c030a030605182413020408010c0906091e151806030e03090402 65
    0x14a115180c0380700410251400c4400500d400c0602c416074089440510702103405c0c000d040c04050041d0101c182031142c90b04544450708010190b100c0281e880d94a04040c2c030f003900c800310782210110380c2c00071000d2240e80d00f41401c06c038003a0700000c0c2c1180c80c5a550400001c804060303010b60341c4201c454074000182844d00c000f81a12200813100208100401c0c0003510080c10084102260001404210310fa062110003400900400e400d402541e4040130224034000350a40002c01000325a1481e602482000da5a405122481042c07803040b00250354804005158641c80c104c4100c203142d07412035185090075070361010400540042d80151806a000241482124070034011002c21100030702c0d019081500d04140145500d890340075920a0824001014035489200c2d42281c010b01302c03501200794080b00d084405003c0440314414100c034040006d0300082c3ea58024440c0d41850301d4480301641c50044c240c4100300096100c0e291a034061a890388085e01c0101180403900c0800307000740075121201050140e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 840515125 1250 840513875 840513889
    0x120c031e2405012c12030d1104061b0201020a020a0b041410170a0b0303040f06180b160804030b0c04031406090d08041a040510060b16020f0118030f02 66
    0x240e044200d01c404a0800036030340d00038030b4441003c0940b0424401038042d4220010055020070000e907101c0c85003044800350b44804001003901114489080008a5802c2c030500000d00841c0704d801c02140481d03201d18102600c0c4140c10300350038414410ba4130312944075400212407200981107400c0261010601340020300380d0440500017240121001c400c8511400e500600030b020444020580e900c0c003c000c5019441d60b078104510942d00241500d444585991546942c2d051600caa240041d1800e04449140c200301600d07031003600c51810701c103450189980c454404003890004100c5402c001000004045030f01c2c1a4402d0190100c001050355035413445c01c0140405040710380c0000309400000038000712400000e0307200c44203d441c1c01c4c0000c103513503541040c0c000101404518845007400d2000c0104014003c00d911043c02d0100c0700410000340c0311f440c4190039004030124185c0c1c00f804041140054505034031480c40c0c03502c05161111154050003481c2142c1005a40222040c070044001c500440c0345c840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 840516375 1250 840515125 840515171
    0x80715020a0c06050921032203140a02010314040b07140f190f210504020a080307030903020108090a020306041403070203071503050c120a0f0b0a0806060901060c03120c031e 76
    0x765803521b020045a07a51030307114200d03520000580810216009400c40700360f8500654000c40c0200011140070205521400188401c90003c0d01c0e00100030410300741c0452150087e90002461585a03882d602c0c1560841c03540c0f01c03040c80000080c042094800e108900070034032070b000b03040500458241d001026003400f070f081e98104140494907041c5000c00c1d0202c414000da082c40014081181c2d03d490001ca41c0c411b10275048602180400207418050580000b001c0048900c03c0e66101c41a56581c240c0315102d080c03081d03009506801c4440802c01056481003182d0449148100303403440d207441940080c0ca41703869035201d031a00b2118210315405036900340c42040c0d48500e41c0441580303003040d9148907a0547c0350081510201d259905034280f0400099800350b117070007401404840c401c64603203070001c3c0c2d148130480d1007606c10b42805c8008100b60344a01394002c0c1c21039141e01c91400803489514018058100303090a50201959038154003940369543c43c001c525070540c01800201e0040390b28079a0080b43d842 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 840517625 1250 840516375 840516409
    0x222a0f0303120c0e1e0402070b01120b09070602100b030f2b1b020405042414180c120f01050117010b01020f03030109021614030306120106080715020a0c060509 70
    0x4d000e20000d83d440b5103010b6103e4401140e0300b189042e0700c0c000080c0082c040c40d20080e10742c01010002080d021401d04140b298140200400111030303407a100007a5403080c60380145001a080b00103500e03032400d40b0b90420114124000c041e1150000e41c00d000d10318000310000c0c0c030391000040440076080129007001c04c0580e0310952070080b059051382d039040c1da4003a9030b1b0f0300c000307000d140c2c0c2d68006020b204a082e0046800c016185030807802c6101c031280440540800c03030355240300701c92100c00b00b0310184903618842c3d40c2010420192641d1005c171000c019038000d0b00300300314005000d550000401c0385028401d030740c081e05400c17030380c83c00c0c0d000468041821100d082ca280303411f55101c00202130041c440001901e04407040b826002d80d80f410820500000401b0b4014024501c00b800c4008001c81480032020b18494034041d101c51401c003e04070081c1703090b03070903c2c0b0412030b20381c000ca00d050080000909400072501d05500440d00214115a41c0700c0994110f60702c41000a14041504002840c2021240843c4000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 840518875 1250 840517625 840517637
    0x4060902010813260d050a2913020f04080d0518010c0b15130e070302240f03061507030201050106020c01020d05270901060503222a0f0303120c 63
    0x106954182c1c902e44c00700320901030404122601c55090310b9510490b00112081a0107000e1420984048009090312109800c004d030a415261840f468480c80f5000c6000402440740098103016801c00d002580003501503502c8440130400030503111410491460341c80d0103940c0d031583d1516007080c500071200b070380c16189041083c00d1034200d010a02c40d005803038021b60f0080d210f100c2c125085000481c806658540b0743d0859050568902e500e10010406804490003139a141103100e00c204004c080c15804050701d401d0000080c130078000003400c1c01f006143e004502030400d1840c01e00102e1081456008000308900503034460380180b2506a040c040d03524965401c0c0020301407007003d80d00180072802407060000701d6a00103a1718006000e20b08500384c4010070040c201320480c4d40c44500040003a0310032105035406811442c40004904c1e00038061801042d00401414042031042180e052182e0742000c1c01d80d101980f5480200d9908030b48614000214442c0c0c41741d054488c0801c41d04020340700d20305018824010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 840520125 1250 840518875 840518911
    0xa0902070305270d03080a1406031c1404090c030e030a0e1909060f2d21170702040525050f070c060c03120509071418040609020108 58
    0x1400c00b06445640082d001c0100110301c01e200700c1124403400381030140d80915800101c0e0145a04581c40c98010042001d0501611501a0755115500820358599415600c50300e1401ca101f10741d8007074012440000e1501c2004e503c2c0302000d130f90b86a0042d411141c0e1565031030780162a119014400e00c60305c10b008034091420508000c0c00a012400e4820305640507482030348080511400d0004d198020303000400040100c1611307011100402c41082c002d4106403100d2658000010100d1130300d40c0b80c2c40390708100049040e82441030103150221400e0400c1802c00e40070341c1c84000104a01c210b40094500c030b0003070715101c8081d40100001d0b95401380124889801c003a0000e90100d0006c03a855410100c541002c0c0e42d5040c14007080581c5100c0c440000d440344096640100712180d02800032007410740030796035000c50b40070003562850898106449220b240c2d80b00210400800c0015000d6458560000380500203120704c2c12450100ca060445040759007542c0c8a9a42c4215038115541d1600100d00150200c1300711 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 840521375 1250 840520125 840520127
    0x30c03110a08430c0902030a0c091706010303050c0f0a0b0603100b10051608030915061002070905100803070b06011107030c120230120913020a0905060a08060a09020703 74
    0xa100306480001e80d1401003001403d10142d0184c0c0300003450340d044115901d24088c1c6098000744000030303103100043d03520403001404414441440c04002c03c4080504466441c680d025602a48804641c507850301440c0c0c450f03500180e040c05000d030424010361030407203140b030928101401e10400b00360540e0100d251908544c5071751a1664801d006040c03908040d5941e880d000f00012240018040c01000018000304100a1800110b002410011040e0443d1005c0d103842c820050100d0104001c80c0040e070048008000300003c0c1e4214980045403460060070a548a601444c00c43e0b00810f800d9074a0201e0b0014840d2035648911003c01c9421080d018104841c15640c803000ca0f0b94a42c40750240580d0f802c4a00720640d40c444021000125646411201c085010301083d604202c8003400d00d0940c1c003440441c01140001c2c2020ac5510034001815428a1480d40110f01d00130741001042001308003040101050544541c802011107078102d4540701c0841c6854000c02c880d540726504803da80380d0050020310700103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 840522625 1250 840521375 840521467
    0x21005180709020c01020f0d090b130203060402040515062205010207121709090f06090c03011d0916120c0503010b06042607091a040c0c030c03110a08 66
    0xd40e02c0c85801599650609108901902629202c2c040c0040002480502032101781d0058507601e104013040c60381075548612004402441c40703406505900075500003170045c9401e502055110080b1424809000516000f0410941152810101d01d0080c00a2503020410402202c0001d060900c000c1041604001000c403d02000300001400080d030a40020031051030388050f02d00c0e040014004001c1d41c640381009101d0028103079800c50042e1200030100381003480500480b07040c1e1300035000d05038540030030041c004004680106181d4560040d01101c007014891000c0800080c0120755801d4a8130b2118142003001e100304d0b6104078030903071601040340d1103515843c00b41c5080f540c0007020410781c5c44200010720310300010100c510740d20703020b401c4020030101926800020424009440b000d06420705030b0a010840d6006c0e0b0303034940030400341c120400000b445101600d484030720170700d071000328900021522441c2c0341c1031860407168198003161800c3c04074400c07517a402200c0d05140c0e4050800d90515801120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 840523875 1250 840522625 840522629
    0x30a020d1b0902070b041e0528080429120606070f05010f0221040c031428140c0f240706020409050105150306011b0807030210051807 59
    0x1140c110390000c1c1e15032100c88101c000409007040d082d544c588480c513280c11142c0040f2411030f072060080704e004034280500701c002d0404a91000c001e11092803c0000700c5d0010700300c2c15184a8900d200003843c0002402e440c0508020b0440401140c18070034000c140f001d100b00751001d504010a001e0003200c1700e07441c078030f084150052800d80742c0c90303036607542e41c2007075031100880c0780001d4503a43c01c247d080910790b0080d0380180b0388134850b82c180c1520407545005981110905690150041e40501002e0010031140aa281e0034202e5060403604590003140b5081030300d03c004c1101000c1c1941d018004424880c6448501e4040e072000d1001d8005045880000b9040003901d0200c6801481c0f00d1a00b160070724050302005100c40702d9840e5003034880d1700d546441d202a50080c0110200fa50600000241038106503511140c036081b601e404509607034410004541d07a04d513102d00f03194510311a45200d00881c900f1001043e00d2402603001d840c5000348002071710143c61014082180c4400c8404441e413040c00c001c00e540b81 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 840525125 1250 840523875 840523883
    0x6050c03071b080607080108061503280b0f06010206060d032001020c030d022502030d0809030d050414070609050112050408040519060908030304080304111503180c030a020d 76
    0xa18080c2c51903241050480d0704208418130402c818441c08640081034a030488907260100d9030f50360344042d54000482004031146405620119805107180c2c01518800104050400100c41c9a203080c1c076540c1c0b1382d01007503840f0b0803c1c604000503c07007656810300a2a9000b4400d84401250300c00c1a80d004121b0513022481c85a86002417402c600560b000390100c0f01d030581000c0c12a0384070115690b040000b50f009540307011000400b0340158480440011810000d1500107003d8042164401015a00650010040346242c0000c1020855241c02880348900950140c030001d00d950aa98a087c1d182c0700300c0b0b800c0030090107520314040285170303400049120f0300c009024002c9980c1c0c94a00d0502d0260082e074024551280c0f641d24034058408448006808846942d0380e2890321507130312140c454480c4016200544079410400000f00403c00500580003030120142400040e0a0115140003080c0c00950761200d26040c1c0d041d02c032810b02d804122680c409801180036044450080d4009200d0210101d0020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 840526375 1250 840525125 840525143
    0x1060e060904060b041d0c4207020d0f06201c0b0a171b0a0b0f0c060403120e190308040f1b1a03070905092a040f06050c0307 55
    0x1c0c10710745468001c0c000300700f0010704194500e001b9214594850451110450095450201c3c40e03c2540100c0c0446400b1400c0c440b0195803900c8041c10160202403ca0685030603031410031072a401a150b01d0700001005010700c80030858606a440d045042e60740c4160002045007035200340c500450500002c88500d83c2c0c900301802c1d00c60404031081130141c40156030440c0c0c4884890070000d40b41020f415003e41e0405030209803100490682d26241b400d402c40264641c1201007400c051110b0315220008200c01d1107954a07050801c031402d102c4510345601218110000f4a40b41c000514002d50b501030082e0001c00c9a02504410b9146041b41030350104020001d41001440c07000305062108100000340380e203030008101442c0e4601802e0406070f440b1a072003410200f9102e65132829489490700203580c081d19080e6900d081d610f180c002000800d08000e811560701400b841c20b40d5104030001901d001c2d0690000003510345440c606250f50460300f509500c94410304c00e003045884100c5d100402118005c0b5031008041e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 840527625 1250 840526375 840526391
    0xd0207060807090918121112091318120201021e030c0c06040b04030e0a121b181a1903151b02010203040c080c01210902060f04060201060e06090406 65
    0x210b40d0002e41d039100c000c056281005c0751045d1840300b0760b0900d030700b0302440b105046400302c001300b22a641241c054041d80c0d90401071028103005103100080c002134600504100e01100c186489400703c40302c2204c1500241c0304030340c004040002c0403440101c4a01280000c5040904401c064444800c03c0721006000c540000000382c40030741c07003000742c0301503408447c203c0e101e5103880d1505190301b0740c1c25a8103a01107002c081075941d00b8a08002810b064400021030401c00316078603960440c03075280c90f01580007121020f020103e503087e05480900311400c600d04000c1a2216151000603180300c40000c03450090307220fa0310000040f40c00700300140840f0f91000400450030020303034408000302402001c0081840010090000d00e0b80d05401845c003607805110140440c540d103044d5907a48043c0d9905550114038008007a035030080c01d01900417405000c1c240007090000321a400552a0303440581543c00c0764501090900940354240b10301d034064a400c0340200c82d11f00b0818001a4003100c000c1004120503198216 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 840528875 1250 840527625 840527627
    0x1051e040e0a0609030c0b0f150f010e040c020706110105100506070609120804020906010e031b03160b040e09010c12020702010e0d141b0a210c091b020d0207060807 72
    0xd4420b158010780108460300b05031030010100712003a2402e6500c0940d40f404501c0712400851004d0140b10010300c180d21104240041c844451103440900e8180700034480f58546580311030040414452181d4082d0204504150002e030501d1544006d07a00d241c0e03d054100038400c02d1001c50318080c0e40c0f04840158480e201c81c81c1090180221b040000c5c0761010400100b1307105508500070b45d006a2007107590049542c0d400c0c00455400d408440c8155040c2d1210815100d540c0d032180c91071000001c0034003540d08401d08a03202c00a445c005a00c080c0c400c010000d02004030004080e8500d410124010007403007410400680100074041d811008107a650340019074104681c0181d4584400341e002405600104030385050a4000740c507220b82d41542402000030410f26403007243c10b59484203030300400070aa594140b07202201c0310b02e82e4125544103848054007141c0440c03940071090005040a0780d0104244101020460422904014200c10355205034261250140c010890800f51203182c40c03c030807030ba560b0b440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 840530125 1250 840528875 840528883
    0x80d03061203110319020d110303040b06120c0603040813170706050a030b092401300b13050405011d100e190809040605060909150103110c0109030801051e040e 70
    0x120381054900403a0003a40201d074150103087e01d521a1103140245c1e50456449200445000782400f140307000013101843c1007a0038894001945049401085068010507203d80c0156420b60396120041540400d0856070000080640300b4044890800121041d04a0352079074240507400c1404404240f0703811080c0b09910440c3c2c0b4140c0200f03a50841d08101b03254040300c03541482d42c08022590950075030b06550041c04410290031102142c02079841901c0d900c4030a04025050107801e441d01d507200501a6681c1c41480117404004800000c1d107420946402401c49414520000607988012000c50050a001c280303a2021072901502103607031001343c0c8445080690668550800c0c50f243c034058030500c00b0703950240c00034040c10344080255988690410130980581c02c1020b034842c0d0340d00c0004c1e03503901c00b41142c900e2000c0181000b00750078a41c03011104042e044620342c40c40e240e5486044505140e489038041d801420280c030245c15503a06154440039140304401c43d02c0c007464950b10741581e5150104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 840531375 1250 840530125 840530137
    0x2802040f09061401020312070e0d142107020f0d0c06170703050601170a06030206030a0e1203060a150c0602040e0f180c1504031b180b0a1208070615080d030612031103 73
    0xa101c112a0840f51a0482a6182101c911000cd20a1686264640c0c03c23000c041d092102e80c0c404034604106965080154204c050b401f40380d0408210f41900d0b00203184441e00d02c000c0c11342c603101c41c07080d8091544c2c800c0e50b5450081020b82010300380740520201e0f98100046020711007101e52100a01e43c1d074000e12401800a41e40001d401200000401807524101e5020031641540082620280c845011120b025400156416a484180031604002582d1840030400001702d0b5030400401b0180d03030b9146d50040342c0103640008030f40540341c0d042081c00b0207100c030020747c80f101080006940c0740c41495516075817400302c05458000c101c001c1c40d00d108244c0c104152402194071412000c03d880d00350280000d60f045a105400c029100f00e407007070449101d10b01807041040d1f00602141c17482c03490b08099807014520702c002621500400c22030700000c600d0a019101814103000c1010568900d0030003010320b08030640360a401014581042404031404542240e2003017070b0546072111000c00140155400c502c101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 840532625 1250 840531375 840531379
    0xd08090a03060b0301060e010509060603091002130306050601030216110307090f0902030f06070507060209271b07050a0b060118030303050603071a032802040f09061401020312070e 79
    0x1485000041260b43e410008500006030024001d0540c0c405240b0030071744003030140d540d01091031000170b0898100030001d981d001070805c0443d10104c80c1a04803c00326809000d503540c40403610704003441402810300800790040800e180031490108c50058101a412600740000c1c140c0348441d02075400c0d5a0100300400260010110400100820080d005d00414105004038003031b0041c00046503070300001080c8544140d4458503001c2c64414240d407648004e50109441941c412019600180d90f099a001044041c10040b540c44c48503040151400314040328011403081710090401c60032000690100e0f410516030b9100f0300d0303540ca80d1110f40040e200d100d1001c0d004618003054080003c1459415000603000c2c1d8407c2d41960340041d102ea05000418041080500c0303003100401c04074402045401034407640038560300c40280c0d03004c201006032041e41e00c25840420f00104040c42489210075034481c0800a11032070748004890300000001035140c0c025548034100300020350001500040c01211800c92040d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 840533875 1250 840532625 840532639
    0x408030a09030c0801021c0b270403030f0e0a03121805150610090e070c020a0602010c020f010e0c0d06060b0d140a090c140a080316021810050d0809 65
    0x1032600080c1810580d220540c0d940000d0003001502c0740b03040c82107030101400d094002c0c09240103162404007070b000f4016900e812069a010345d10400800c1c0d081a40c0066040d42c1103001c0d820a800e000b4265965403180294032480c001003001d00850000d41d42580315818102283d141101501c00c000402a183c100d005200038035081d0000c2000200721400b0180042503111415140c00d414810701d0104040200d0218400351002d0101100040c03429500c01c10500c2c00303501d50310305039010917100c440560110016030b441c0d42c240c174a6590184140c1100d070140000811070a0200b0b450140d031354018804241c0210f941910400522100307400441c0039210035000c1c5036465a00c844440018800300d81c2d10080c1e04042d6022075406441800340c0e41c04560800c905000d40c41c02e21408540781da5400c4100343e13004407905000102006c06201a0541c00c41c48070b07606a0100d50340c0103000c560310302145040801303146181001545d20701c0315059002d0324015648400280003503e0441c889104080c0d400394030801e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 840535125 1250 840533875 840533887
    0x9080c0f010b03060f01050d0602250620030402060a0f0210060803070c05010c05070e070c382e08031204031107031104050a02090d120f1407030c02010203040803 71
    0x3815000b028600d03409400702c401d02da6445001d4440c24401307005013030703001c002c0300210700c08034090f5006048241e03d00300d1038800d800440100d030002c201c80900100c1d1487e0315008400d090886002c2114041c0c0b20014a062551820b640001c41c20305c240c1c04c00c101800f950100c000311f032070302c208030100c040840c02004004564039410751947d01c0d040303058201c0e040c020385a0042280d51007003500344181640603000700309070390038920700c4a004880240441c04010740001d04001007986c02c00807504074442d01800d00207030300e00303501001e1000b1132440603052400900c02c184050302c116038034003402d4403074010298502d03000f10790780c50f03540340c0c03000c0c4c0c460b907207501c004110111350f0f0701c010f540a07000324030a03220903000c01030440406803219900e1001918014400c0c94942e81410207402042d0310554001c4010318154001c800203000c4c7d050004c055580718484038080c0c100c1508a04184500003581c1004030813254201150101845242402010013007502405021a4000c00c10740d40984031007415261181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 840536375 1250 840535125 840535153
    0xb03071212030e25050d0203150c1c05090c030102030f07180b07110f03121204021f08070315150c0204110d02070507050618190e041a07080c0d09080c 66
    0x81ca11640703c02d44c480703040c00001a030349001c803d41d441841d80507000c0c0014481c40c4061b004803140082c055a11a6400c2168040da24544804100200000a0001000d0802c640c0080c0340c0245204254000d80c27040090140d2106040d03043c07540180c081c54015090940001e2840e40700da21a4054508640b02250000807c41901c000c90302c41c100941c0c203600d184d205e40d0b04040d0360b00600c1c2092076508108005c550781c1190f24500c0582e2090000c1c0080004400540003800c1c0f02c6500603003840000c40d03030014410308a52500440405200244007031030201e0905215030b10582094010205000c3c0c05194541152a50f404c000c590030048565641c503911403c0c070b114081d50213600211001e0140800120345850960280c0f840e05d03404c0401040d45100f50760511203989403511100b03421802d03141000820140c0441701038030882c13083c100c01c1e45400103040d03070038100b541c05860700003841002410068ac0c1080340e42681cae425a5040000704030f0f4215801d08047c14401c1d084141528051810080405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 840537625 1250 840536375 840536413
    0xa061503030806030c0a1503020c16060807050403020f12151006090618090b2e0327030302091c050601170f06040206070602040801021b010b03071212030e 68
    0x180e019440b450090b6881c0d600b0191202c5403a40f00950010040b0303030521100c806207003c0b14103c41c990400600d0541e8110616103020fa02845400c00c01700e0080040c001642d004150640280031030514034201406e540c0090440401100d00500030700001c907540c44c6008080190a02042c040001000c1c907041a4643c461110b01601900012032400d9100080c5a807182d0640d050410348a4820320a2505081c0340c0300260400070750855001a20280d22010078151604190002c807403c001e5800d080190540942500e1001a48103128031095210b03400740d80441102040c11030b418500160760b0a200710005400301846812610f0a14020b02007030100140020402d060340d07a0402560400744056100381c3c4e6502c4140c081042507008500401c0041c1001405010140c0c46103402500b440d03150700f020b42c2241c010400c01446030004c0d071888600a0001c0c421091503c2d03003600a880309504050200c0815290b082004160b804030751529140703c1d109a000c042000214000c0e10f40700a00c00c03030b2004030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 840538875 1250 840537625 840537629
    0xc09050102120403020405070e03060c04050a060507080901081b1218161701110a021b090106141309020301120302010605030d21110c0f100501031a090a0615 69
    0x10450015021a8660002a40b984142042c1d00580d140600b9a420f0002400020b8a01d070207008000407011110303a0188156032003808402a4541c880f85440308000c1408400e40c0501c09001c410444040841c014200300d070000d0800b030a103444030ba101c0d14038070f0b501a403441c048900c413000b022440c491440c1ca880b0310f2500640c0d003090f004c03118403002038259481310341d290850702c03112400c08410840c036030007202103c4540111000008a44d00300d404600c0d01a80b00005650060304200304a0407042581e0350802003005096441e1103981d0304010f07018040034000544200380300ca01044c08409422800d012002a01640e4019505c3e96582c100c00454a000d5800840255081000204690034006151551041c4560721951541510340303a6452030246900c24848032a217074610754141040440080210f141e4400041002c8a0004005030030001c400c0c2c0504c1400d03050100410114849182707a4401211307481491207241c40d5090311510340709140c90010f21076401d0141c40542182d00b5020343d42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 840540125 1250 840538875 840538877
    0x50c0705220b041104030f080f0307030902090f04050d0c1e0308060a29180d0b09012009040c1b030c020909014508180a23220c 56
    0x4079807000d0000f004144c602101d10a03450f8442408204042404007000e40c1c0350301d020303400a918111810707031106042c0d401100e000c40403070b03200c2c0c10103021810b0103445558041c40350140d0755a141030540e251a280d8900348e22900821800d00d80d545d05201400156614841743d512041c000b00c0040c1c907001d088000e04070b030014426100d2090016407084489140d45643c6040d00b100340041d509812080d805400001c0724501351042c0080e10003c82d203d190917820782c076008210043d901e2074001140c0d0300f520340c081d180c0d05000a09454103400e1682120554280d124204c9002c00c00f20003000c0200ca44644c3da01e141002180000c81c40c0301855005425074440030f00969130b4014503568036003250b080c1c4a1200c208440840c5452240c5806150b12500d4240c0124020120400b0040c5801c4103800f01e2200303000341c440c40c0000504102d600a0741c03c041d014100142c408020315842c0c200304000e07240141c00584050503d4959407246507031030a6031a0100381c1004024181c200081c1321100040640c46440c030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 840541375 1250 840540125 840540131
    0xf020f070e07032d020d02040e091b01020d09030f0314161a060f04092108060f030606030a1202031605030a11010b360f04050d1e050c070522 62
    0xd003420794505504c0f0540d00910607140e40c600f407000784001c0294451000c0f4070740c0a40c20300010034001d00340050117019221805c0100040810000781c03140341025109400c2c195440340125071a2030703400c1074032541142c0e048205081c0410f403c0c142690110a079802010969200148080c048241c45900c01c20310b134091150780010107920001c07561400c1c1c0c00d8034455841400603082c222985003607004412140d1141e01d1100110954030341000e0140d21151500011650030000c00c5000d0500c843c07030840c107078401c80082c502801d055010a40390b03036681c14041c00e07000381c0e0341c24000c54a008004a03400c80c0c62007039080c07455080c030b070504d40d45a0700201e0800000401d420320045107100140a01ca800035001000010301c1145103030119215200d00040500d03005400001148a28010000c1c61040c40c4552000d00c451826251007420b00d40d00050b11410320605210282034031007000b040700d03040e03551400d01d81e03901c0812100700c0340f0308411940150f40c8481c0300e10038000c00c50702c2c1d00381607200207860b09028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 840542625 1250 840541375 840541391
    0x703200304030b0f092b1107052b0209010b0405040f05060906010f030b0904030305010f1211061b070611011a180c04090e0606010e041b0f020f070e0703 67
    0x603200e00c140c0c070001c2d1000c103512012400e555454640c1c10307001590181154200e21b0224060103101e21401c0f80c09641004600c0d04600e105e8000d01c0c00c1e0114807600d005020000e0030032002403a8502d03009600c0c001d402100c1c0c2d402c2032800805900000442d0010804901581e40740040b03406984940565409581402c00a44007440e50f0700809006000080c50307507030503660768001100c501200f15240c0040645070790144034070351158551103011701d0099401240da507041002541d2000807640c0000e04019411a2003004101c01500c030000c4204200c1c1c403650b946030446803990300110820304030721050081c0e810015946402815030601501c07407800a008045013a411903456002400c1402e402007841c645520180420000304e03984240d00407045070500740c03105200c5040302d0403654580300356402501404419a0010400722850500725810300202c94203000a020b02140500b904061210042c2c20210242c000c2c0035440c1c040342c00708115560346603181e000320001413055a5100110f8a45250 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 840543875 1250 840542625 840542687
    0x5160c18050405150a140a090201140f0d05280b040b0f010827190201020c0604350a11090c0c0703030525060f0c0306140103090f02060703 61
    0x307028071494000b0082c04911044034903050228000501c80110070741d6507405014902c0701e000500303000e01010000091001418030001d0549038038001140d6454030148511110508007404940c25961091000f060340c0c0c803409100062005242e48075081454651582448200c1c2c85c0c1c440361115904440c00d100125010007800052021200144d00203659103000440c0322184194000151410319009880008440e0315a070810840b004210030084108880380c0541da0304000082e801a003c54859241501e8174035800c1d406079450010300030807402096200c4041c07945103100b034030440d292800e80c0c901428903d800905c1b1191013820610610420010a20026000303042d10b000c3d0354001c00819000f81140c5081d6015040b00c0d64006142d03680702007090114040400d216034041c801e40f008922480e1011051095500050030342e0109440c19104001140e0b0002101202d00c07030a090000b448400d43c201964905044440a90041c0300001d2840426601103103034a80700e14a07035100c89029400c003403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 840545125 1250 840543875 840543881
    0xf060e07200a02030607082a070f03030603061a090903090105090d0c05180f130c090f0209060f070c060219061a041a030708031e090105160c18 63
    0x3240e1000a5201c020700c2001d09114080c0c00344010400d04031120900e80d40d0000c1e1811030103d84400011b0320480500010032411030312114031401c050940c00144424003040d0b1103c1c01034100141c8103881c101d00410a06002c1d9100300041e64201c40103004203030321a003411040c280200b03100c500070103800c40001c0e00e441c000300a440003000140d41d03003854040c80104006203800320310303003d881da4000c8150019855075031a041c039007254070140003580180742400c0c3c0030440d544000c100e10b074903d03108510080060082d03012007098079030860f03000a095041e100306a009001b1680b4a80d0004000205030b0012610000a01003c9100700c00142ca81911108101d881300c80c0800d9004110300403050010000e400340e007040e0280908040c1003503040000400047c140e402c4414050318181c1c864884441d00d0030184401d402511040c00254a841404c251900301000c182c000303245403010125002c12141c0c4540200c54070b1403046807202c1504411810304030000f03000b920411040c4011084551150380081c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 840546375 1250 840545125 840545131
    0x7080712030b0102120c06070c0507090c020a030305090c10050a17040c0806060d1709040f022206090f0315020903030c300a111903080405190b1302010302040e0a0f060e 74
    0x6805070407e51030741c003070aa405064030407048600d8064002c000c61002e10740e01c1b5690b10219154004d0000007424100134044890280c040141da40010320581800d03220000c50100d0009d451400542e241d2000b603044400c46005a801d8074400403ca080c4003e010baa541d9007000c0d50b1208040e100c29455a40401040c0050801e0082c110a00082400b4202842d08003800450402910100700c100d42c404003142243c1c445d041c107902010020100138915141900c003980a41228141000050b0030322100c00507003001440300500415012201d00b45485054055819120010302143d03103074061040300c143c0342c8480141820590414400007113591880c0f001d440c07400100318819900d1b20319aa401100c000d10030201c0011070f44138240c41e10b10908212000300418502a030303100c226500701450510306007107841e43da240400400080c900041034162903074940204090448919049861005802a008607400014a8803101c0200300f0303d450243c000282442620604000c002d031143e0122078a10750903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 840547625 1250 840546375 840546397
    0x20601030314090d0b04110103020a0e060c0a05060c0307030b0f06040e0601090b030a06080f06070e240406030b091f120f05070303051c06140607080712030b010212 72
    0x51401003011078001c0101c100d507020402c2c080703443d0120000100380b00e0710403000203d03003a0314a00100000c1c0900110702c01080e030f200b480c042d45010403200c001000d880865a40901c520000900c210300d2083c02c1104920b004d9002d03080d68400d241281e082e1003d0341040340c0d41c4011a04000d200403062170070600d02150a0f200078403041c207103420000c400c404488024801c42c144080c2d9000820710000c10341c0514860070750b040b004a1450f052516060a1400203c1c0240c81d5500440901072415000b404210250906450f001c0100181a40306440145d0342242050354400003c0e0100340254160458001540c003503031081130580303408100c0300c030340107040f0213032000804a1202404030b00208030640e0009400751400e403c0c07070103031070f102c042c1480c50544c0100c4c08070380001440044070400840300c0200d203000b41c0c03042040500e0303c0c55150b01c82c0c0d01070b06010b00c982c10005011040003007071419904465001503440481e000318140150003001d2090056015116200c2d212020425100403150300e00d400f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 840548875 1250 840547625 840547633
    0x100b1c1407020d033b010e0319030b090a0c0504091b080105010503060904080901090918060c050310030f0f140a0302070b04060e0f010504150201020306150c06190e1e06011502 77
    0x107100001760640055104c010584000e064410014509000d0b045000c110300e8040e42d0783d1650044e1820380500741c03d441304145410003042c1d24259803803006050303008461080c082803400e00f039070080f2541d1165070004509980b030007480ea10318040710028101d000f2107988407003603140d0303e440c010b490602048584a0780000180c0c00100010020350103041c0c2501e040c100b200c5595290121036007528084115924040d45c004184420b00246000c2d0090740c10721402c0c07151541c10103450640c03c025042c08050004114114064100718002c0c0041c80e2098120240c0b0408403102441d5503114180d00d80290b00510076403d0101c2d581da46201181c0c102d81c0f940c1c50b0090004811030070710040b000000b00c9241846070078003000848207050004c41b05504215400180c2d00d180c11010030040014441086480000601007001c81d03d4002812640040207201da50000210308a007600207452041c0c101601402035507035900c400000c020a901001c05988192282d0b40e0302c40a4204113142e001200d4030060344 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 840550125 1250 840548875 840548921
    0x61103030411030726101503030c0503090a08010906201b0a06090c32041503060f142d0c12010b031e100b1c1407020d03 53
    0x469003034a485203202c050140c0d415290b4811160940e8901c907000740b0040c0c86654455200c3c40c60501c01600d103980c41c1001000103110021405c0c2210031507010003010301144418140510004000350381c04840014401c0c203070a5210690603018281e4001e0454009003072010a11441c1600c1e80303004500c4070100800f50929000241401d64012045d503540000e0041d2480200410701d6401240b09540c0100da1503150b036450704149002062032a031901c0410350f08400c84003111041c80c2e4001e42c59510488000c07c110b454040c003144150110381c0001d00d01450034543e083c02d600c4941081c002d03030100048041842d41c942d007810a80f5094001110042042c503104401ca48510f1071900c0d4101e1111a0111305181100d035144c0400442071700440300d40c03480442046092004411900000405c102101c1e1032030a003203000101507045401040404c0401055803541820481c2d00111094400300043c400d12502141e80501c0c030009890080043c02444a860702c0507009009170009060700c10441180b2070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 840551375 1250 840550125 840550133
    0xa0603050c04111c0e0a030203130f320d2913020909031c0603020901080313090b04200d0605180105090c280305091f0921090f0611030304 61
    0x110f030041c070050f04c180c1c2c908408460540c10404840074034443d400440d522134070101c19840c00c840960010b5440800c80b601444120058040d03a2140c858840c4d0280008904100c4103c003114a180d40760381100e0440c0c9a1014003503050f155600741c1c102d4883ca101e200c80c1013052007a05050490786101c2503410b1060309001420900301d103039401070320342c0709503424a4151072424104c214040d08200b42c050311140140305608c0c1144180d401018010019440c140703030030503090310a18880c460550307099520701d503814058450343c014004802c50b250300c90140012001b805000344c0c0040e03044090461a02001003124140740440d002e0280281c3c40400d0241c0c2380200708103082100503c0d40d00313415028841c0103c03000150100c0c0b40380d0b4081402c9080f00001d40744004007100d4004203018115400501c80d8151a4102204040745140810f8045040f19807824805e18410303401107000c0c4860707044003c41001a50040414041c1e900c80004030700c11594800c1c0441d44100da000d1582d40d1504104040350001d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 840552625 1250 840551375 840551407
    0x60c08040b0c0c0607061a0108060102100911030a20030a2f090c070203060a020a0c03051b060108100b0d020105220308160c0e0906070f05040902030a0603050c0411 72
    0x1081548044401500f142d20204400d6040800c0444c1e20700e4907000e000001300062210340040400070700e00780c2c00d6440d2520001795a242c64001d4404019600c0c02c80034244000741e00380074441d2101608403941c809403890046032070700c0400c60b01c90440b1040c0005a606140104d50f452885030444803542c2540d030034410105641c1410841411824035902441440e43c965480c418810020030038110b45072240f034010f160921b4001012008110301c1086080c6a49803c1000300060a0b0545401a01d0714081211114412810424103443d4462040002403091000810445134040340c18107000c202200710502c8100040420000d002c1001400788003a43c008114103d858028259444d221081d5642c03200391255002d002403500c0340541220b15400e01c45517060110007840c1c0140d0003122442e0145040e500c8800c050b01c550704000d4110400d400042c4242c0030b49014050003a4110359034244041c0c1040100010f100c00c072582e0040030a0103c031403038507100d20114902880d221914001c0307ca1120101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 840553875 1250 840552625 840552637
    0x3041217070c060306081504081b0c031506010f05040b030a2c032a0304050405060a030c0f240210020d0f0906390e0a03050303040b010f060c08040b 65
    0x10008107000c1100401c40d24020000200380c10386000074605c0c1011041800d11031006050790381c11180105110000311807030211888100e9135208ae14100089a03442c074240b03100c9074040b40e850312034000c44440505a100710907020300401d885900c0045a007403010b5545004511a040c9a00e0090001490002c1c02d6041010340c0c2824000c030020000e00710074610900c42e401c0b040742d040755102254405001b40c254441f00041d450382e4400a41d40070501a400d9034911641c0902401030b500d88020440d20745a1140b40409140c0c0300c810450803945415200740b1861003031040400f80e200d085100307aa5079050075901340401c004d40e40504081850848428003035440203001140c940d40e584068011a01d0034030890901a01c5078801245c40884c0c1201f650f002000c0554060789010160782c0410341b0392401c814101d00c200e290400c000f0b041340040c00100c5092107544050001c0c000002000204108046802d058660050203220840c1c2c41e485c003245c02400c9158000d2003000100000c2c00049000406409 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 840555125 1250 840553875 840553913
    0x80607090603050709050d030f090605090f1c120e030c0f030a12020f160302040b180414010902090c22081f020d060b0a020105090c1c060b040518010e030412 69
    0x5102545ca101140c8034072001c0318148d00140e94850b5442d4103a5006d4030500003005a0703e851820b095550002901030f100c1c02c06c80d41d00c10304402402044c40350000c043e1a01c410740028100c40b417071f0706140d805030500369041203c602c0f03800785002c114228078200007080b00c9104003038020909485a42c3d00c03102a500085c1602042d407068040140403140704201d8941c08d445940800c0030380d10310714410300c02a034940e041c400b8451554130305000480c1c80c100c2070f000c1d40150494601d543c0c41515048150052160507000307900018104100301d0714842d1800180b40d08a0800c2c800022614524003c0c508400307280184040c54115100005100c44610040603904100440052506100444803400c581103940904c242503c0031540c80b0120b034081c071a051344071100a0162030303d10181c40010341150141d2602440c00070444001d60203010b219405201f0410300a4810043d9044c209400c1205030100d141110070ba40c24002102074400c004019502100c0115030401e0001c010f680d600c403100100300351222 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 840556375 1250 840555125 840555137
    0x50103120c02011e031d0303071403100306090b061201050103051023091e0f07090906020702100905040e0a0506041e150c0906020c030d0f030917130806070906030507 73
    0x1c84c58032007070800c1145429180c400142d20903092050f0000c03640b004140c2c1002d5003040c000c002400360000c40940194002986240d41c80d51042c040d420102095000580354501c2c12544808028010051901803c42200c01c0d00c0f848410001040c02d8030b000f400003d00c240c00500c03071441d46690300e40082070303030480f00720388064a0034001c00340c080060705c200d940f1060380c0d02c61364500c1c0c0e000e1031481181e42c00e100d1b100b0242c00c503100180e107248d50341c0404e44209070845584d501c0b40400c1c0511581a42c4070030ba0300620f49083c41e4a001801080d4100300e0156a11507403828142c1040d2520002c0c00700500c544c0302c0041c04048d0b8840d00c0311f601000c2026420710001c1e484e42150300020700c0580256511021107800050307409001c1c400100740c900640c203c00c05551140600142a0313800040a0680d0001c0740f420100503850050100e019100050740188010f90030f070380c0d03182210102d00282034050700700200c0d01c0788580e5805c0615552503080d03905201003407601005015103882a04180da00c01e00b907083c41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 840557625 1250 840556375 840556397
    0x70323061003110d200a080f06070906020d020703020d0206090a090915050112140c060c01140705041a0a1b030e010e030c0a090b0a0b0c10050109050103120c0201 71
    0x154100282154848400900e41c1070500c1040389070b034500b02c4291416560814044180c2d607481620903009015403024000c185020409130340d5003541c1030041e000060903100c140c4098400903607548030541d0304070b01281d0202008140c03d880010b00600444241d8004c021503482c5400788014030304d9000007603030488000c100b840c507680c86100900c030041000400006020001d800c0003800b44002001c1c2d06649824900100000c11000000d100340c260000404034071101c030898114a4105a090310079001f500204400c40d0212043d031000c1c0340a040340740d0b041074a65801c84101c1c0d291089019a0003c0000300c40a0b440001c05c06000c2c143d10006410400904410070403003988042c0c2d007010072000600c47c40443c20a550f8010007141d11480282d0007408a0182c000020b807440d0f0365401403600701581c0300c0a21003540d6584c03041c0070080511070305407941c0e0307104213940300c2c0c4401085142d84100703800c0000018502110348103480c100c07a08130441031410031484c10210744121001078103904008a054076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 840558875 1250 840557625 840557693
    0x10c0203160f06030b030706050702010e040e0607020718020306091603240302100311030a0c02070f0f061d031c05130b0a0215090a0f0516080303180d020703 69
    0x4844003038000c1242d20703010300746414001415541d11045160294000681c20001250020159004268242007924890316060082001010000a15a000e206d0f090034014903d0b0040781c0c0d003042c0c0c0e0030200399600d1404000003090992100352a04d075001000b400014008035003d69410102c0603aa1a0200310240c844c15440f16202403410440c03c00395164000700b08500d00f0f2500c03140e820b0214201441164007203011203a260100400d0349100303a88030294840364a01c244004030140425900380c1041544820140d060301910340288400314003001d18401e51910f16101148090100600500c944402c08804050b40c4c5d00d40d0681c4030900c07900344444040d41c0c00c0c10001f10064658540e034140c031201c034034400a1030304a04440c07001d004e601d2030081c0b00b03100501040180d501a00710000500c0fa000919007686804803071410042c8031000c0d11000306480702e001c00114001d01c041118070790b000706601c5000d516420031340d10b00d0000da0b008540800c0007540c00c3d009800b078000449002c111903409004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 840560125 1250 840558875 840558913
    0x30501020c010b0a150c031805060408030c011409071509050405151c0b0c0f070803040f021f050307030c09090911132702150d051e15010c0203 63
    0x2881031841c1d455100c00d403031504007540f41130018111803002410b2030903031a40140c00c0540541004e0b00b0002d80c600d44034400440750626070002c29004d400f82da41c0c2d40d514940c2d5034880d001030307445503029401d00d101054125845055580a0002075000d00b11251504a034036040c61136034200300f070a100100c40002501d5407144911407291a41c01c2032485805251000c101040d24402064925114180d4090f800316184050f201d40c040a41001d07541d8070303041213203540124012110700600440c000401c001c10051902d0072189443c0c425956841000c0d1080c62a941c2e4107000007440340014401c0c80041c6c4045d2080d000140807600905000040e03c0d25101c80130b0070f41d4407442e02900c111040d584518024101100610341ca0440260204030001d03101da03900c582196031b04880785007082c12040440075941c4d1140d0203d541000240d034960b94992005002028047c1180c43c101d00700070801c45e10b0f10311562000a03500c5401c040d400e040280e0361a200544011000101c2a41c040c807403100400740c444844c1c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 840561375 1250 840560125 840560137
    0x100e011b080d0e0d0f0c020f0907050c0f0304120615151d0406030f02090712150302031b091f12050105090d1e05030c070b04030509030f06060a150903050102 69
    0x107116907a941c404101400645800b0340503410154004421092400d80c402c03030500d11514a45001c584110780c03070001442c00c00b8a150075031b034080f10036820b006c2c54a40060041240002c003400b40c8a151b200c08e03000f241c4a005502c2580e0300810704041c030b000090456800031064803046200d40f4112520b8008004a440038114400049103800c55000402d8107000031060980b401203e0078008581581d03580000d040302800b00a02032400040031a440e01d000e4040e404130109810400c0108504403000c2c8018410030303100c01e80c000c0c0608014403030b00003080b490080903840c0c040c15201c21a1505c0143d81048070060341d00904001705070b0300101d400c0f840001c0c41c4038003070b014100205d035508000e02c00b5820072094015841c00e015981e82c0c102881c00701c4c05101c00c0d00c8070003401c08031745039520880504100d1181717100041800d000d00301000101904100503041400c0258101c843c0260490b078007a0781ca00c0241e856541c4120f0803082084100341e48406130884a4503464920f0546a90b691154260380000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 840562625 1250 840561375 840561383
    0xe0a0f06020d0b0405040510151814070203090d1401060810060e0f1b0d0b040e010c080a020f030c07020301140114100f0512220303051e06100e011b 65
    0x1400b00b040c40102c1c010092042001c68040203039041c01d644a598484100a00f1a1519107400c440340c03c542e4006588030041c181d9a01c8406030190389456200149074440326801c041a00e40045a20306c0d10000950715803070005000c071510b4545940f6118030006058250750003564880c040414600000c1c0000503580108000209805080121042e030b0000000c00f818021180c0104000702d8a0a11713000c41039a09410160b980e4134040003403e00058080c8075652500305041c403000040e1001c05600208451401c1c0e941c1402c0303030300d07000070310b1099214040503900c8030706003031000c2101182d02c90700811008c0d01c010000140b1881041081743c03840e130300340d00628104148041082881c104404803001008980c5805038004010341805841c034020641e40c2003134000b00c00700140c00c008561480e003956400105413560b14116a00e001405064102c0307000c0389554104194840b03a80800c41154020580208040201c15031980c0413900105400d103501c1c10010403049844100b0301c0380c64104255801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 840563875 1250 840562625 840562627
    0x3122007050709050c0a080a180b091002030606070303050604090f0503040f060c020117060310060b1e0405010504030f1a010909120908210c0f031e0403030f030e0a0f0602 75
    0x1541800c5003000381941c410310303030242400c01301724500f01d000b400c0301c00008850400740f4003915004940d900130420452090a555800c00c910018041c8100000d845112081c2c00c848020008094110503400141c0340c081e00100148805070001c0e0182d04100e5001c98040c00000d03007a00c1ca61110316000802d0b510a071a5034100040c240300324808018503030007414903400c1c080310540d40d581c002000d0300740380180d00f050b1810503404944d665030700340b018011410340c0080602c00c1607107a8140d00c000303500540c824200205030180070303001d8250b510300707036030440f001616400d041920319141c070000c0303601c3c0d00805c403540c488090600d10111100d41c8c100f40a042c02e018002800303241c6151046030303000220340040511240076010010301c400059003400c962485520510160241c07181002c0c540955049001c0500400c5080441030000201034451201c0c0f003007120481900e404240b541c00d100714040600010107440342503070050301a4200742d0701c5406000c116828180c042d05c0f9034444100055048030b009030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 840565125 1250 840563875 840563887
    0x19091a0a2403050606180f1513050109032d051903030f0207210210020c0c0f060703020706140705100b0915010804060b0f12100621031220 61
    0x11081d5605a00c10550b424100600c0c107000300091746074091004450314644100004204075140c5580621030020060030010141e004503440039000d0300091007000e03400c4180c6900140c150b11658540d012290040700a041c2c24500a0100407001071403408800c00440b5599803c0000b00f080200c1c0008050200d07800754403800501e00141070701d40400410803064014406180800c0000b006c4040100c903540044008031605003003039042c04a07140c01d000f11144081a40954103c3c0271501c140082c4084403100c041c200d4140421180e4041c02501130010780c0907590500c84640109103083c00340184214003810011107940302443d0401c8a4450702000c0d445109510b09401c1c200100c0f44c0020004106803050301c4028002072241900820107082d29481d0314480704507445841c1036030090030000d00f44114078000030743c845a072809500b0313108640c9450b1020000d0141520945007a4032442c1a41480701032686440032908802c4103c6014482d95440d1f64045803222000b2245250b45042d4070110340340c0b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 840566375 1250 840565125 840565169
    0x111030c03090c2d01031a0909010b12010209040509010c0f030902010207030206040602150702010608032d030408034c080d0e01031a0307060c11181519091a0a 70
    0x42c64000c1c990600d4185508000760103e0151720f50303090781f4140c0e50400e4903964120b003a40540982c1031031541009000c410303101400070640046c1040001500c043c4002d4960652040c200c89103600f5840005880d903c0c0941100e01c0398110065060051040783c92507926a0001801c03a40203500482c050f80c400f480041c9480103941c4096403004640c0000c2000b03a182c640600d0300d074070981c20342801016250040760b8480d164041d50100200d01000003c0d260701e01480c016509500c140c2d00c0096403400182c68001414256000000610851481c1c503202141c02d0368102c1c92070f104ea030300d08140c01000718000c503001030704101c2294a4507041d42c401142d01064000076088901d440420101e4014140904441e80c40000d452000c4581500e44a200203529003032130101c410960040c103900c5040d00700303800180e018024034107010340e10310099882ca101c400010429038032100c1d40d400710b42d030300e0f800313170030050381502d03502060849800140e109454cc00c0c45000402442280d0844c103009040e07002280c7c441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 840567625 1250 840566375 840566449
    0x204180209011b051b040f0e060702102903030702100e10090e070507020102031207022b09050120011b1107060503040f061821020111030c03090c 64
    0x6411021051981805130300d0780380e01d40c9180011000e0300c0151760620f03429510b5540c0011040c0c080c9010404c84800c0702c0f17000c107449034000e03516080103204010103001d107511207104000101494084982c0003404a0113125103000030112560f915010521180003d40c46825030344120f401b0513600c0c1250309801e4000c01c16210019441c02081080602d818814645a0590b00d80c107d905404e00c9902e548161004038554414491200207440582050190340d81e0001180c41c8108001e001030030880c1030072042c0480e03a903a60300c3c200001a402013820002540284403581c03074512081c5c1c4220400459882030390a5035007001c52007c3c84103c00361084030580d40702407480319000701203001d40701e090300d8514001c2c400e00010b44003600c2208025000010860203600403084005040d40c44810035203141001038108003000208010120354010b801c04407403040c801c00c0030030030b0008103003400c42c0c881504004c071039007004190074802d11030110300d84a00d6490b4402c148140040041d200e2880030000045904 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 840568875 1250 840567625 840567647
    0xa1d0d030c0302070c300c06030501120f0209060f04020a0e15041a030717010b030603070e013204020c06070e04090b280501180b03030306010806090a020418020901 72
    0x109032060107003500040d01700765217000302d80d4070005e800d80d280300800d91201e404400219081443c61042403010400c400b02034003104a034403903101044240e9035180b004418070102c1038002c02c07400300011680300501c0c01405491b04440042c003010840102c0b034000c42d040303078480034040011810b2101034500c03901d05041480140d04041840324103103860b01e21100d0500c0d091005103052101c01100280c0603c0c490740d080d5000c140030001c181c125582d101d020004030790058a42c1800390088180114100d0540d0300e5081c1203401c00700300c180080801c444452101c5a00c0c0204141c43d880c1c0c01d88599050340c50b400a80900b07289400603101038141281c01400701e082021089010701c0c05d1044403030200e041203c003241c2c482803400b059020302c00200c502800b080c901c2003111002601d42000030610118020030b900307906215807800c00840c4619400c269881c0004c1310900e0015440304001401d50800701150303508031010700c00140c00c00c3c1d11003171049520810100c440c514180d002c41c541407650ba1207440445 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 840570125 1250 840568875 840568877
    0x118060f0608031e0d060e04030f0c0305091002070807140a090c021c03150f0602010e300706090308150d0209070503070903020904150e030c150a1d0d030c 68
    0x200307451601c0300d41501c0e405900140c10b0b2a619544a01d0b4001d0070507002c640043d445035004205140d162038000d525400d042c0c40643c0084d0204840e034801b180100280082c4a415458040c24042000204030300200141c0c0810110702401c2400140c101c030800620f0050224070341820300c40d0489000b404aa20000da102c905a0360400352400c94440d0086030030021041007200460072012071100640242c0390581112800d0207220b080090b5440015500c4030507610103500910032130b043c060310159144c0150307000e406d000a044225800c190301160b00e41406c1c100d0002c155050402646521040306c0420300c0903030108030701030304001800c2d201c10410010018201c803c12240021900803400109004007241c043c880000081040350703000380c0c0044011540140110301c149017502d001043e02410010589240d07080c400b588100c04004001c0e81c1c402e0040030b000307200c036901500c4e1603011200c0c090060101d1b02c0c0ea50019408980c00c011040b8008003003480204001271188000408071620a25070380 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 840571375 1250 840570125 840570131
    0x10e0c43030e01080406090b09010f0e0c01080c092403071701140d0c0801060303030902100e2d0a140108010b031003150608031b06010b0702220e0118060f 68
    0x100009400400c10140b101c003c0c40d01d031656548916050b001807850800180a641c0354400b00020080150010200340d911170806100c5e20319003000540d507403012030048030f0104100c4030002d800c40400f0b50207841d41140040920a00c42a01e20048205a900c440705454840d000400c00848680082a5200c00300d2002a880010b6160650440d00203011040840c13091749080030100038001000707a42c0010740100c07002000115621301d0050700034011890128020040c8904080c00d540c0507400b50003010344040c00317200b0301c0c3d00c00380e03142016070300c0d020600b80021101c00346c1005a900c4881002014001c1c070032524814868190024001d884142d0161000c06003c000f04442810501b074460212980040c2070140c6861000030300e8050510b50700310b00307128840030034920140c021460354241c1007480601038861690301c44030790545030300c1080b801940081b40101c144520b20b5041000c261070740c05042000820340c0541141c60300f55452030742101041c688400c0b0f05000d00c01607101d4000c500000003410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 840572625 1250 840571375 840571507
    0x30709170724180801060e0610020d050714060c03040203010f0e071e0812030103201e121002030a0e031e1c020c0610090c08010e0c 58
    0x800c0c1201d001c00c44102a0203a402da0b002902501e01514080040100d110059807135040950081800d07201d92490184040c0100f41d02d4141642400045190303540604018010f840301601e16921203802250064003d0280c1e650a400a21030302e401150800841c1381c2d01d0502d80101801e44040f030f0250240149000c41d44407020800081200441d4682a1004500408501041002c90b800c0d445107030507014501c042c0e1014984040118140e074815000620300780100000b45a02007a5220840d42160705006881c03e05200d00040100415008181540c0700445100d183d05100444014449158001c001d00c2092815801611400501c0354019407c0c4202c0501c040c41c442901c410111910b03034000741c04101016001c2080d032024191840556840040c1410b003907840030101d4040c8c9918100c0380c0003203440e0b4051700070300d00310349450b6443d02c842d0b9003000c00d5201950b2014004465400b8108514800284140c0203003501d41301e40c810045000c0007402d894a030300d001d1540c5916000c2c0c064804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 840573875 1250 840572625 840572639
    0x30102130510050d060e010306151503050c0d0911030c15071202071a041d0403050d0b060d110d0c11030a080901091a040c06030b03030f0304020d080307091707 70
    0x9000201c51045946140010500710160f0f078034840c07401c84503c0e090508a0100b840c2220130040d50403644240b07010410303a50781000d511211503050040100030885101c818607807501c00d4020640100e40401e526182c40399202303a1004a40403510103d80c50000400c0703841040c6028000d2540000d000d54151b071420117041c2584685200d445001400700c3c05443c90307250618030030080b100240c0141c0c1c0c0c44200c02d070038010461849070814802c0e07503481403558008203c4020003000700c034002d6505494240c180000c070400d15010b081c0d281d49094101205019105403501c850003001801000140c006994808010b40c2d0380540701001078007401d00458150300307404014008100c8440706080d01d04215941c84c0c1c000c0081c0075219034040a080c4003c0d01c007170048050684198140a580300342c0080441940d120400d80070b6414401269a05030405d001002d0101100001954000d20007000668031500303540c1d402d0400c0d0020b5914400180a03440c0510160351070703502324a07106c84140000d0490300d01c0e040c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 840575125 1250 840573875 840573907
    0x50a1e050613021e0705030c16031b05060304020409050a120e09061005120727360905161d1b0904090203030903070e0702070f050f09040f080a0309030e030102 70
    0x2d1310192010300040e00109208050095480003a4a0300c152400072011001c100b1600b00315010684e8001900719840110851241c0500d04407940a401c031800c59466800f044000c01d6044800c0c0c17068055481414002a40407050161100f541d440e494424400341e82032090715200105400d02411401301030004690700b02c41640c0003040c2c1200c20280603074130100121959015804405440c2100f0484850021240070407201541d0000402e15503440e11810742e2030039501e00342200701011181e581c8103101003030160408407846002d14101ca0300e641e50b2041c07182c000e4000d41d100000000031030904402200c070728038030140c200c4184034017441c8580010b00c12a420b4030454120301c0c81140d903083d40000315141801a0b602c10700c40201942d040b140d88014008100303104807443d000500a000d00070076580d26040f50346c401d4810213080070508140d90407c1c000c0c01103018100b90740c03001e1184e070f18000241078240201002e619507980814032140c11300c1c001d009c41c100030111a20990040c42000381c003c01c1c130300e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 840576375 1250 840575125 840575167
    0x1d0105030709020906040b041413150306150b03090d080c070c1503060510030606030e19060c141b070608011d0403050906040305010509120a050409050a1e05061302 72
    0xb503030069481070a04001006881140c1c001081960013041c00519241d050310042e036060801c0d1000350b800b0b8010a41541101d0129007180724071083d0360300610100d40305601c6204120101d903a0686650303242c09000003560421901ea20f210b501800c440c01110307138080941034005420f60400350418403155183c0c0010b0029019102031484ca5900c540007403446604090005c100181001c4051050042c3c02006411280101000b190800108002c40c0e00b0001d500200c84817000320058254038155a001c1c06401d1621480c0c0030000d40e10303403010304117101000820040c8024000d007068991282040d07420400725621400521040c0c10040100c0100a60700c0400c0140004070480180e88500d02030f2a0341c0125980c107034006102040100420005600c118040c6030244121025042c070440040202e11442005e403000031800e01003000b2000e11500266000180b1680c0400c4031151040c41d150404151061640c000e5111f0082c020242000e038a143c16600b1100004d514010401d605030400312a50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 840577625 1250 840576375 840576389
    0x307020a1101030906050106110c010f0e19080f160f030206090112060b0c160905090d081005091608130c1a07050102040806090f0f0a140a06151d01050307 68
    0x70705942600d40c0c03080d0704c01a02035521240c10441945c4413030300202511034000701105148640200e00c0880e6010b9085190520095a00c0c80c1250303a8510600c9240b100f0001c1c100202c51003220085000003003400b02c58802081800100b1200ca4a0000010035080e5a40200041344105909002503100c240c101c0d4048402821f10a00800400f0800001013040c1d61003030403001004141104600c0020800c80c21202820600900a41d00c441e000300445405490a1081c1e42c0190300d4905802d01030070745c050f4002c09080004c0c0b0010707691307030100d103850004540045660300c0d40524401c0c030580060115420480c1c0091203c08800c0340e40d940c6044070080e0052050700c940d51605280d44000b0b56040340c5000d03134010002c2d515603540b000025031ba402c080d600b80101e801096500e41c11210005644900084101c005019268068561098003081002d00a94170300500500310041441030040041c4425200250300c130b0503141880d100890903280240d48140745440d00100700c140d80004190090b1010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 840578875 1250 840577625 840577643
    0x90a06060503281d0d031a0411070b0405010f0e030901140d021e13060c05030409111207170105011103090f0f28051819060915080708030307020a 64
    0x8040c00d0002e498000325003043c400383c02c00043d042d40080c0d02c0c43c02400d2040c220b088990710800c07000190142e0354000c0240411400ca81348107259843c4c10340010b40e010a04450003460300d074007074591200189044030144c81036034482c007404054002c0352003220a8508124061800c104d61100003d2030b070041d078090900e80b10b00210341c0118101156045800041142188000b404080c011204e5103411620408440c0703120303c1d00004906004000c2d6074652640200503500d4141051441001050710380100c800030141442402034038440c040515000321a10f4465541c0c810b420804485a1a816008241005200319540210b02030010a8960401c0304841000b0b8203400b510128941d0445007580300e0348440c010021041c030310005140c585207207039a21002d61003292210248046142c6d4400550480c402c0d00000034420781046000c071010402078070000c51840c0e134588012080e50820503070442611050380c3c0411910500300102c400074040d11004d54118504400045d40303032000d61601401c4594 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 840580125 1250 840578875 840578911
    0x5100c021f020703110409020a1a121311030f030a0c080721140901050703051b1c0206060307060e010507150c030e0c09010e06011d04020301060e090a06060503 70
    0x565030800e44040741c0c0904000d114481074680007590ba04461200f51040d41410320801820b0805d80505106a50050b081310b510300c1ca0300ca04582c01040c1458139140860050241400041041031700a006015510318442c2070300c0c2c18140351504a11802103079110b5404402d0546c0440c1020042d100510f40b03034200030452003c0350030f00b00400c0c4140280242107142d5104d5010342d00d12110550707100300801e50346a550340c141c0030743e0048070341c45490409400704606100100c00a8071440081c0110f1020030b58201a8003003841d10303549000080b01540050501c0300645c11030650781080b03103039031122081b002031400701d14000d070150920200c00021810080e0001d20702c001c4c8500d040c03d2000301c0c40008010400b03414600002002060b280e4410300c614082d030401d00516186c200a824140c80746014410150346a1500550705110140b0f030158006054040c1e181c0c8640c2c541c40038600900c8d143d150b61908810441c104504504001c0c001141d89152034001d1007041c1c0e01000780c0342e021010b8242250154 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 840581375 1250 840580125 840580129
    0x10030f1a10032702010c0204050408041a091807110d0f030f02090901030602031308070309141009180f050108030d050c070305090904080702042d02040e0c070609150e06010f05100c02 80
    0x4050341e1b00a0741260901e4140401c0010000080c001c0340c5401011000c2105440c01483d00792003181842603014441422003118600c40c0c18072a5000000c40c00c000411146a011890510103400c0519000c00c144150842071942c060103450304d0b80c00342c40400c41c504046240000c00320401800090700035580407000840040c2c402c6803008000b500b00d4221034813503a082c507008291244078024107440503080720140000d4100550081d4010146131254440141003c210602100c20a40d680405503100e01c3e85901c030102c81c1c45001c2c080c0c0302d080301940d6256000380d62402940c4014004030140c1e8802c00480c0046a480007d444a0001c111982032450301c4034100115103024064000e94410b00c0d02040c03800d049843c4030034804030002080c01a03010101c0c141401e042780954815040c5000300750000681e660201002010310b103200b260000351408a640310b6a0010003a414100032032079a8607241c588180b0200043e0b0b00424807540000d00e12070819002c14490f80725071603500b05204007010088219 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 840582625 1250 840581375 840581387
    0x190b0c0a091a130306050103020f04050f04120516030e09060d051510030611030a050709121b0f080f0c0a0b09011b050607020102070b1003020a030210030f1a1003270201 74
    0x4030303c40328403006280d0300c038108440180000c1c401280b06201da1810351826040c2401060b01c031302c40e520070a2045a54a4a900d02c0700161200c480040060801101228940ca0142580d0450003507072406051070010051042040300500481e2280004000c410001000005c44521969101e00c1c8000c10351036480e865509814a90401010782d420014060f00001c040c401561254035041d03400d110a84902c03030b0540f44103015018182541710250042c40c00310340c088141c814107800b14411144625982c1c440c1c20030503184ea41107400543c000b00c0110400640400c11800e0690701100c2030303504d240c41d114800005102c4d60a26505000201c003148404c00010703038000110719080400d03102246040c12000b4000c3d031100360308a80c400c0149010503040c0620220b0101034960142c042070003d4115020440b85d07036900c603960740406840d20132403a045c1286000700fa0042c40c04c202c0d182c902c0c070809000c00020300c040340051000c051804202105215000c50b45442c522000200c00f40b6090450004803a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 840583875 1250 840582625 840582637
    0x9030f04260d030e060708060603070c08090d050d020d03020c0304050d02030c04050c130f180504080c070602150a051b0913020f1201060c050c041d190b0c0a091a 71
    0x50790242c51901e10b203141e01600300001a030701c0c11007550103940d6000742c15a1503800a551042d002a03041c4005950b20740640d035852200390144180c2810601e01c60005090461001d804a40540104544544050f010040003401007424181581018031580d56282c0c1c0e0300030b038400c0354440e09010b0388603010345d201440085101308003d841888280f5100165136480e90043e8001d0002262a140002c1c0320000d1550800c00c1d191601209424006104040400b13032602800a88017008104002d07241e040f801c03c10039004100710303009405c0c7d4a0120601c1c0220050061040705041c1c00d080c10032107101c0030140c1d224a890b004030449502d41c045400851032442c24400712270340c46031000a1b405110340184000e40032054000c004070a03160b0700c4180444007407109403c01045d41e8010302862203c2d00e03003508148100c0c451074242050305c2d000558032902d4001200c1c00c031200c007906c1d821003d00340000b2055413544950031680c1e10349400844c450041c54501d00b4030411801910031f0b0407403c0b0f4040c0b1403080b0b4003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 840585125 1250 840583875 840583949
    0xc120e011205090141100b0c010b0114070b130c09060e060406050d0c14061606020a0f020f0705040e1606050d0c03090b04080306180a0209040509030f04 67
    0x2480c6801c021940c02001c0c086412031002901e0700d22584004105c0b17020f49110030038007000c0c3c0140d601000001a90980240007120502d6640c9408607502c2100700c0a840364000444c00462a690300e08000341c41ca0541d0085018207000c10480c04008c5180c01c0380c0b044d0041003a013040c8815400d80d080000248400c1d4200300391550400200080c0e0360301400810f401000d044070b04120f0640d9510400440002114004043c001c0d402c600f001070380c0301d02b1200041034501a10880c039151032060119941000484116103860703020074001402907000d4900b005504141c002040300b0700181036103a50703491491140c1c61041c0c0d21010303078102420301404000c0c40c1040c85440c04402c581c50300c002501c180c100350000c0e00101e10384180c1d2071155210740113401c0260b070000421007060b22580c41d1100c3c00d90000b0810364002e41151030544210f441c0c2022030384228994080141c0b521030a40401050f240e018040b240c0a5000340a22140850818101c40445109040c0301c6000781400700c5000b402040210032903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 840586375 1250 840585125 840585131
    0xb0708070302150a0b0a0815280501260703080f070203010b0411070203100c080c090d051204080c0904201f031406010c050705090912070615060c120e0112 68
    0x842c025940d60820400001e007103079402c01c866114103140c0c1c3e0f00d0070064180b4501e40104230104056000d008860782d240000704402415008040404c0f80907034070300ba8010301000703a021481c03c242441540030700e4410074199014048051550300d078204030740201e4400c040d04400c0001c40c402190f400358844015008050410300855400d1031220f41d05070481031007a130103801081000124150b1504c0748070884141c130744986215442d404020100c5402c18490300340c202c0030303507005130012550030065001003408a80b1403541d1035007010030481c00e15058080090045400100740b200080c0402202d1080c50704919540c840d900802c40000e8110500340d0600c4c0d083c40a2132511100158190804581e03000541c0c00c1d84c078680c8070940112011612184060281d8111003014080c600e0546c0500342c0290306034085644d03561a541010300664040310741105c000c0e554215a4000e9a00c0c0540f85004110034104100c1c03034481900d070307920712209088414040001c8405900c4642e0f0040300d084460040f81c103410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 840587625 1250 840586375 840586381
    0x2015060a0509010e070f05070f0f03030609050a0c0f0c02010503010504110909040b090105071b02011202040f1202100305060121110a0c11100c0312090614010e0708010b070807030215 80
    0xd0b581000300f034883e030002602e41c6c056151214000c0040301c428075801010744055155685a061803403288a800310201502c6002c0022000b4140c00b0740e40c01000203280028a100940c1400317019140b90501030414810408003030f20240c7e0300310080c2ca044403c01c0ea0302127160480d800a058591140c02901075003d6000342c144414801d142d50b0700c40c8100700c51002004035407900740c01651840402f05064050510508501e001944a14001e07445104c914001604154a40d03080e49600d080350b8100c400c4a286c0c805040b0198a042854a4140b40380341c1410803140c100880001c3c8a500c44200e03c030800d55000a0000c8241807030341c000034001181001e0903441e07034081c1078002c00c070031280d020030b8800c0d030703150b61040c1004e240c0782d07904001003401e03515454004e585c43d80d0300392145140303c0d8910130113580e0360075880c0c081103a0f0b004000320003036001c840c5011581000300b00d01d4641c0001d01707018208101080180203a400c3c0c1c5003190419074012581c00d84815003480d0480c83c040c80c419004c0d80e580700e40802c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840588875 1250 840587625 840587639
    0xa030203070308130803011e090e100f060501140c07080a0804081606270503030a05071202030307090905150a080607030b0f360907062015060a050901 66
    0x24051042c882d80e50020651900c801d0030740b0300e81803440083d182180c204010070245072982d0b4056071486150390030b50750b0b203a41d44840d08110344101030701c196150003008080201e40041c1c4a00a0301c02c0ca07404080011604240008051000080712000cdd020000112108070034030802c20700000780001c80071110074980d039207085801c81c5c2080c07058248a2041044030401c0b000c2258072402502c0c170302d940b041e003000e40c0000350a042924192403d05505080fa2002c10303291001d10046c04191100d840389903131808507141624182ca1000c129108640040c0148403002d948038002c84100d504e481e4001c50551191030203401001829481705038400b015000000319820f010400c54820001c5440400130101e0309018810000545450154040d0001509041020319107c1140104d13400c4000980510032080410b40029425100d1503525840420f04005551b030103000304403140305000c110b070714100c0c0c40519283c1d80c01520741c02825100e117000000b0b01e0f03912540c0030080182001442c0f80c0555079a804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 840590125 1250 840588875 840588877
    0x201050d020a0e01120915110d02040905060901051009030206032509290409020f0705030d090506070926161811030f070819020a031a0109080c0f120a030203 69
    0x111450108170112400350204a0a200388004d507500004810180c50301303801d2001c01440d04404c00c80c07e0344024003240921503002c1c40500040c0c1001d03c00000c19040582c100501e2080591119200d81c402a40c2e0381c0d06107038049002022280e040c1c40b030b5a01c0f80c03228400a40c6422029411400507554441c000c0134540d8021041e60480c0c49481c000c811000c1a6040d111007064950302c42081c4000402c410040c0303009070341c001c00d42982411441424007610b5030b01c0300c0c11940400d545800d80c94445554105000701407003034540000c090300307040541c18a403100e0008240c4130b0485040e590403076000c03401c0030850b0601a0340d46460205c80e4000c01d40ba180d450902422051904401c110351925030f6200030681c103030003120701503512003d295a595076030150454121000910415003108440320083c2c40140c0ca001404c040724068070f0202e40c44210881710148021003c450300e0400c4403080080028100101c4c40001401c42507443d05884480100410f01031581d403400d1500c40d106880c10381e414181c1c080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 840591375 1250 840590125 840590147
    0x905010204121b062a02030312010e100e071b0f0209011710020403020319050a17090102010f05062b050d02030910031407052203061d060f070c0201050d020a 69
    0x503c0c1c03c079036140c0c2000c850880c0b0402c850b90b9082c045004c2601912000400d00b440540b008040300d103050550340c4a90280351703081e8801243c1180707510502c902400d842c0500005020429005102854402001448100707020350340310045000c0300c0306505004102c1101c18207203401070542c004a584d59407050316075080d0041114940d0080904070003c0c80014001c8401300e03a0000c0041000380d80d00f1302c5c25031000c0501c24003115144180300c50480001c4072004a000c90141d8407204a80314060b04c0006401c0d03560b80c13111802020315143c200040c0b41d46140032003000b940200160703d00900c0d02524410141440c0300d024040d4840c0508081d170380c0760b0010003800b407030005544c2611442c0740f028007501a903070702190040059404100055080f0710450160401c0c0400601d1000700c03110040d0300040c1800c0c0c0d07070401d42d5141d84070f076800b00e4194260a203000c0450103203402050a460b00700000c141c03440020340710300c013000310074a0488250781c455400c2d100000d00b001e000315900c0d607030100042c0140b0404e07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 840592625 1250 840591375 840591413
    0x20108090102270f010c050c04050c0c010c020714040b010804060e01020702040207060b031203010303051806070218010e01170703122a0506061002030d0c110a03031e09080a03090501020412 83
    0x3031340c0d0461555201e0000d2002803030f4404020031480102004220140c10001d00107517602c41c0601c00c00c03840300d100740900e103c001010b402800700c0c1130418907120b05241151076010301903070400100100c2c51368802c03130306940550800000220b0362a00203000b4003a1084050180d8020b00101d181d03400d00070300d6402540c2c401c40072821111100654208649540400d10024011503020301840c500000c4c20b1880c001000d80003420a4604411740e800940310500c140c4460f0346001a41005011006100c21440c1c0944800b80412202e40551081203550318050b000c01004800c81740c940f01c4180d40249050a4419000002042e098082c050000e403002424001a200c500c502d0002c038a8a050040391150031411a80c095403421501030125006040708a45030420041e011040c0106440e0034011030261a10a950104800400d60040d4011400d1548180e0000d4642501940000c45050440356960401d0902240e0b003040e82c01c0450082c01150711004044480141c0d55040254020700f888070300c211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 840593875 1250 840592625 840592639
    0x61908010f05090708070c0f0f03050717030c0a050f16151802100c11100306080f07050d0b1b07080705010c08010e0601110a0515070221040302010809010227 69
    0xd40e0b01006401d00e010340301c62000c0740c00c0c0f40c04194a903100d0503c034842da034041d41e0301e0302039030440f41d5580c840c40301c1c2854203400080010640a0400021001300304901c41c0e4041a18194141a2401c01070b62003142000001d000000440a000c00f803110140e600c0c0a126814080100c0e24504000342c20b1440300c40300e500c00502c0e02c00d000c2d202e09040000148003a80280402d11501c200000a442582d4008070075074810507101039441e0301da50f07003410328208040660380104020785400020b510304200d0740008011030308070940600007034a0784154000740d1034100b140c00440341c60700881d40b000320000d00c00404210000040042c207109414004002c0180b0404c02003003418604903089030000c1082c000e0900c2c124800021803415886201c00071810491402610000c0c0303081e6071400d01d0643c1c0350a00703403545c00c50f40c0d0400542035014070080300303408110b01107041911030030591207005110320b020090500c035907000810f10b484000d505503030400000c610000140f4040c0900c01d201405030070a024400c2c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 840595125 1250 840593875 840593879
    0x220e0a02091014090d06090f08040f08030c25080f010209090106110c011101020c07080601030c060f0206070807050705160e0c1201090216020307060c0c0e0906070e061908010f 77
    0x22164007250f07641d264804405040a0b40c0b04100140e6a41d0080d040c0c9540381c8503440040410403c410302c02d507041c429031019644914110340881054080d0f4812007071a0414080c0e96074002010400c03a071020000c048046048103000009034920600350483c038840d1054040c0c454081c94154000c0c4148401150b203511540e0381c64008860645851f0508440e5800c28062481d0550141c100e40a001600400141c03d01480410035450000c280e4040d0b641540590010001d100740803440c040903009600c3c101c802112a210080e5a924001c0d00040410660800040f29103100d9415540d141d07a009040d83c44030042c80100500440d828001c1d004544400700108620200d0403003100c1a2950300d4101c144c07a60b1800090343d009400c003070003440d4041740891040380140c0d800d01058000d4500d5446600344440542003096807414540c010448100a00090140885000403140e82c40216881c03d401104000808100035001c2c4840c007060002d000e0325804821508140110305030b0b15009a0321070865 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 840596375 1250 840595125 840595127
    0x512040c12050105190c0c4d010c02030a1101170a151e030809040f0212040b06010c1106070303110a09210c18060b07060203040308060a0b220e0a020910 67
    0x50065840c900800c0765a140c080c001082c0c03000300c24040041c00180c00c100030f0105080030b0305041480d0601d0000075407520f14a01d602c5a0f0b400d015010308d0030b00e80326400e8034582c4e010907512081008080c5c01b00c43c4081e03810f0807a130312800800d10305184030220400c0d94202185450b001e000080d0040003200800f00c070204801c01080b540352a0328003040c6812400d01d1643e140c0d030b0034941c4541800e40d0016100e2110000c00441400103221b00d208040c030701906442c0c181400300c1c0001014200c50704010b005440702010840004803400c0c01081110b143d40e80b10554503007900100012130408011000114440e0940c40d04032044d001202c440806401c3c1e0760050000398400070f82480750051450031082028400c03510008180440751007020000540d103500d4080c0c0041c2c41e0003800341268005d40000801080552211106030403c0d070030349548070f04070b0805081403414012018003042c0c45440d5007510004004540c40c1d01e0041602c400580520705100c847c60b0f01a50040c8521802138524034402d2040d6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 840597625 1250 840596375 840596381
    0x11a0301180e0a0812161409060906130305100510090b010302070506010609080c06131203140301080c041d0a0201050c24040204060b0f07151b0809070603020403030512040c1205010519 81
    0x168415031f503960351504003a03060600b035041380754a583c0045060140f0b2900340c51f0000107000500944141c00c41130b0f031540c0741c0030389441210b543c0d01c1ca1180c00c00b0f09011240d4040015401510315185000c01d5290740030300120028003620308040c129124240002404c0e60300300030120300b075a01040c29524920301d01402d00c1440e100d26607c8000d407001d004820009030f15a00385c3c4485241c400d02d0001c81d00b01800968400c2a0801e8000320301c1d80e00114242d10303080c0740c04c0c89845100d04020180048810050b125561030b0b0b070b052400079043c8440010300f5256001c0a100c00c1c40c0d080c140d2018188501c585185000c07000c103044600b24083e41c50000e01103070000c856400d4400c02c042072a0a03d16012a60340c8641001c445007030603208003a11105407000509090940700741910203681c8018991034040d1a240c6808490303880749081c180304220a0001c01e512000310790705144410360011940c0c4941c5440b402421031139000e00000c104c3d445107041046410340003e8041e0800401c090301c2c2d84183c1c50f8090803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 840598875 1250 840597625 840597661
    0x2041b0914010c060917030403120f0903050a0c1b0e2217070f0b0108010c09050f0607061802040c08041a0717040312020f04030209011a0301180e0a0812 67
    0x80f40700d1607442400111280c0144004a100c0c8141580031041403480700540d40056804034041850b592040754828403d12442640d01c13019102031208034002d031030290071445051300320010440714142ca042489080342079480307100074000c2c900760002d41e2a42142104141940c442c00c40c002d42d940017406400605d42d480000d15040115000030001c2d40044951590248208460940ca014614070200320301c05d40107030003400301c64004100d00c044000001c0600c92079801c420b10590110800c58540d03280c0d801030fa482103512402c000352030380741d102601c2421816040008d5000e414000e020366103e51166415000701c0c89942250f41c80840401c440301010320440319813002031224000d50350206184014245c1107070090400050b001d0385d08030004280da2014001c00004c1100150402c21414880b0455004204000d01d040369018100120402440706115522140400740801610003155611030340d68140020b0884100d108107280182d19900720250040d80d4606103400141d0101c400a600d40c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 840600125 1250 840598875 840598877
    0x3140a0e0316150c0840060219050702010822290414070e0c0403020f011403010f09060501030b030d321902070605090f040902041b091401 61
    0x8109502d09401e158402038080041d6824102503812851500701c5120301d900c070322080c1d03807035030394a1420741626490a510044008990480c0025070000e80302d00120445422000d5003110f50810f9181c01c0c030070b010f4001c141c1029043d070040318100000a410500400115100ba00e800001d03580c5c05100c0d1000020042c03103180c1c200141940080018146000c9003100000710715501c10008d0488244940c81c1d608440455802d98000e600c005501010032080c4001e041d4032551581310715020301000c810b0300440c8402402202030341411103280c0c3c00350000c401c1c3c0040044109407250707514082c00382032501602ca40c04503685014404a031a5103e8011440d104030050014042d000c00c8403421544c1480c1103c5078100d82942d07009034880381c0407e01e0000046900440350684a5401e4002078110b000e00818084c2598401c0c00c0822520f03800000b0781d407644408a40c2035264007207c1b804907000c3c100c1020000d41c00752400311001c84148200c1c03019800c40c0420b90b0341c0401c060310b40f6445c450213980301da4103074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 840601375 1250 840600125 840600127
    0x305070c0807080706060b07030f02010b030304081b040e0607030603031d010e0f0f060f03090c0109210615081005060105031003080c0c030a03113a03061503140a0e03 73
    0x2804103100303c00404c4107500c603c42c00980f590f40c55440f00c081d9000303000700300c00142003182203402c040ea09019000711203500728043c516151804035140d41d1940054050140c0c101c1c8007246070550f07034a50340030000340e800b01c80a0341d4040c54080c40050040c20076010071804150384d1210b10b80c903075508483c10707a15114107071581c8051001c0c4000304501818500c04003944030049525503400c40d00d0301e4028040342500c000c180c54403414420881402c180325800c11314108003a80078204091405c42c608103042d01d09640c81c642180d030803814104042c00b8480d12038004c0511100001456650004200c00020440b5408000d25201c850044809120030b0302d081e1600340700c0e81024408144c80500800d0740d040d0070307421079400343c04c000082410200c04e610241c02080c0c0050701d4040c2c0d60300500120350303d400c0c4e00141049104100d030780300184d5010703210901c240b201280d40740c02c4140d00a03440f14004d0b25403d514401c00743c0a405000f000780c142044090b090000c1000807501d070238201d02500002000c400051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 840602625 1250 840601375 840601387
    0x301113411090612030406120518060c071b03032c030705121c2006010602060a0f09240e06040c140a172a030a120225060305070c08 58
    0x250440014080641c415841529520700880c104000c00c010b00b010382320036000b0303868454000d04032000207080c01405010040e101e039403000040703501580019030b40f5103152120200d00b02020071511b03600a00001280c03013040070041c160461030218403142481380a498485a401c0024418290184e840344c01d688803030001d00107842c16030381d4145469035423022a115805030450a1048040781d0320084d0110702c080640e80c046c122030105159400d40320500600041d490300000a5845d00c0c02840309201664604075040c040ba440c0e080800e8258014a0791184c030124840c4180403d5501003051710b80b0742c5001800f0b503ca42000c40c1e080c0c45660040c0d4012a1035281c4406085542022035480394030107100c8001050700309041015480c1a045d000041c810200096503000d243ca01d4207418100b29007000d19080044d690015040303c00c05d9106602201d0942d000c4400d030325001c003d030800b0180041034041c081d074442c4078500000849180d55420701540e20340460540351001840d502801da15010814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 840603875 1250 840602625 840602629
    0xc01080403140c01060b0c1203070509150c0109060c020d02071a030c040b071115042904170c0f0906131107080f030906010b03190504020301113411 65
    0x800c01e07542c091006083c0b600031010700560071503285400c4950b0078070700840c0740407a80808110410fa002c41c2d00e0340c51851400c11803030180c958040c40c40352a01c034195180c0328000c2181d05800f03492880400c40000d11002c103181c9000c0015045010b0840f00510403d01c0b0002528030014024040303d1446c02a42010490030100c0c25403a44014428040540100000030700c000340c480043c07500c035028480b1408119880820400c0040c2c1703201d2100c401c2e1100f13000c00c0c030141811910a00c1c0749003100b8121144c00450284c0064140116407016101c0e03080311403481810100401c00c0400210101c4007030f03058034050b9080001449040e1050b98202000120751042e0014540c400944554071902403401c220113690f07100581d13805030401c9046100302205005110307008111042c00b6082d9007803554210b01d010366480082580743d42c2c50000c4182c03207601041c10354030700b90710090f007200b01351203426a59400011980194200b4182e280d40345c64000325408440305140005562490f44049882c19042c01002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 840605125 1250 840603875 840603887
    0xa0509120106170303010f141c0f060f06090f050705160302012703030e0a05030d020d0f061e09090f060902060c010603140c01090e010b0a050f0703120e0c01080403 72
    0x1098100c95940e41c00046002c0da07201d4000701c21409202c000719a81e40c10708400e014100c2d0705502901c0944c11210203070140340c6e5001d4020030302c08400c2d07020000319121401c1400101003261809480a440c114840400341010b030044001d840d98094144946002190f4500440d81c2c11608540007580502c0740e4090380b5101000d1540e064001e100200d894016070b00b95181c001d40d800c29241c0504005c1e402441059054000c0000c2d10750800060078042d0115100c0716100d11504006620f00e550014444521b501194010540c68041020400605841d21401064004946114820003505a0002802450078052911151741c803030790b0025a01d80c1a91600d010f0210b40000705d034840000e00041010210034440c0400441c007448255210110100255082c007402507012410000007410900c0768000314200703641100c61011007d5640e400058084070300d4081e42c2c09144105000040100c14564414103101043c41e08081c00c1208600090300c80360f0f81c0c00842c03070280c0403c07401030000e000710307000304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 840606375 1250 840605125 840605149
    0x605010507110415270515030a1202100219020609061e19050906010326030c0a11071712030108150612070e010e071812110402040801050a110a0509 65
    0x7132100507095103c5109a0a601d120480084056690720407409003000300d020b03154010010300412101905800b01184d10350080d180080e0003204030444107050300f882000303800d502d0f10070080c1c00c41d101d0740d140500210003444040c07000014490140400c240c0000465103501a442d551135008051020803071609101200401e0310608548400000c03101c0c03041d0303028039882034460401a00442d81540361640014005024241301701c851429650749019401085036040840340d4107031500e6070300c0000201e9800503145600080c42c0600720340065120303a0014548148599131040d00d0014a80745109132481c0000d1103800b403d07501c514501c594507501c6119058000e00013070400030154603100328a900c2c0800c1507110a0011803000010010440040011038002020f450f2500c48200713052540e50a240c0d10340505008402301c64040400c0003a025a010360b040c101520564940307036103c083c03600030311080316442415820007400a0044a641d002c80761300070b0032070b1940e605107411002401003803080c0c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 840607625 1250 840606375 840606401
    0x7080f15060906032e140405060406050d0b0103122105090a2418080405011107030204090b061c0b010b09040f090c15110705010c0807060f050a06050105071104 70
    0x2080741407541c0d03c2e040003d41c030503820b0b02681c070b0070300022008036405100b80b15441d100b02507100405208001a10140600d403100c100c801045039210807001a00500807603101507403044480720700c0c008000007400d0035412070307000702003503c0000d0002106480c804940200c00a809000c03c1d2040b000c0d400036400160004903110803141e1000f40c60742c030002001c031101003480801c0101d6a49034200d4485005001302c4294550800c40b07610241e0340da40c503d0340070358050541484440807001a6509007000158025a001070040c8071050309400c1802c010301050b0f60090207080f241085c894051114076500c0001c940c031901c1500315070b06e81182140f8941081040e00d51050300d5800c943c00080060082c55a800d0242c850700005501d4000d0003031234040c098040c1c0c400d01000c641c1c410000c0c0c801180d201c0c22940203003841078030404c25142544041c86440c0c001000c851411074507900701250f1780e1000c2d1140c5040c2d8400c000349601c2d02d006403040d004902e0000c5c07101100c0803240c00759081c284c0100d0318006503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 840608875 1250 840607625 840607627
    0x1b0207080703080a110105190c26130b130b0906040203060109020318070306060501180f030f080c060f0108070911030c160b04260403020105161b0b04030b07080f1506 73
    0x40505d10b017511815540caa03024082001103044040c1c0c01d100316050b0030440d041c0011051760904603010f42560b01d2180e400000c8079440000e5030301490325015100c0c83e5000c0c0a0f050107140c40319400b071a4020381e20302628800c08100005240304000034159000310780041c010191a86002107007006580018001503101c0c500040502d89400704100440241d481800003140340740c10440010107280404034400b04080340107804016480d00e2100403025640c00441954000050f410a070b00b42c1e00c10100b40d41c24501c10501042520541c4001803816500d0000175103110f82c0d503450a15090b01c0400448482078001040480c901011100081507580c4d00c20305c030f0300c0d020407081e2903c1c0039001c001c0f601170701ca001c58090b10101880464000c40304050800c510341d4181811900028018080d01c0300c02c6e9a5001e0700d07003900083c0400e020105080c0c0395620760301865a0f8441c1403550041c2c105200803100c40a920010400050040c03015502c500f03480c220715413059480001d080e242d4103050b4038494010300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 840610125 1250 840608875 840608897
    0xd020f060c010509010b0f0d11010c1709130c0516020d06142e050f0f040203010603090203120304020f061623150402090a1e0e011b0207080703080a 65
    0x11400007500d5000009000002c061500d01040790030b5401c0e05194511030440c04809030803035130768800030481d40750300300c3d00b03115182c0106030051780c04800300356005d03110f03085038402d94400d034032000010070a41c10281d4640c2c10840c0b00713569460035284010b1500002c1141070101541040c1c0303240c200c2da040c900040070458000043c2d201d2000b1280000210100e01071400100400c1042c140440030044007421003210404c00845406849002d840c000c0d24801c06584000e4070195035607001503c564100284110360b00c0d45c1d0340c10040c0042640001c00c0340603020b82401e180e402d030a07040c141c07845590060b00e1405002501401c02c0940d81c802d49410581c00024a50540880c00134a64910300050707040010407100c0140140a240100380d800102c2c0401101c800c2200517120a013125030029600400491b0f514110055807c84910015005d003050303161551007078403030405401ca9684030a00100c44100b480c0840d004030380301c0865016810042d406a1410000100114011710707a0110303514008200301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 840611375 1250 840610125 840610129
    0x50d030e040f0903080c070203071403011b050307091202094b010b070c09050c0903010f0f150e01030b13060926120a0c05042607090513020d020f 64
    0x354000070035081c541d0340d80c6018040617002480d9036005118421054102880750380001d076200030500610540700c9010760031141548007508140d1001d05103400760072642c5400c0780014003503001254080d002803454100040c4c443c840341010040310b82c003d05245002d6540c60044914001041d40d00c11080c1c601d2054000d40d0400000c0240c0030201c40801c005100320b0905d180158440c060b000261810b404002400006010549030000c490f00703403002242681d00c4101d40940c1c0d008412046815500700000d21000d2481a0301c2401c000f070903444108542040405c201c010500140a544501c440803801400800c00c5c9a5140e075200204103003030700111040343c0c1ca0005481c00000c0c121480d07240c010b2201141420f00d060b031240c803030034141c20a042c08051000f4481c07048000e0170101ea032035502c11409004a02c640f040301c0c00307004803404075032036102c0580185143ca0b22030254140723940540b0381c6c081042d0000303006150050000140f00c4020030b0301a000c11085001081049030701c00318a0602e901c1d55 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 840612625 1250 840611375 840611381
    0x5071e0b04080301060305060906010c120e030304060201020409060603180b1302040f02070210050324060403050607020f070503010b0109061d130b0909010b030304031709150c0f0105040c050d030e04 87
    0x4a12442d2543e4495262641c0030303007912006014544221604400c10040340da20141003c03001303822200403008000c1c1090161000300046400e150180000034002c100760b60150020801c82c3c0c1e02d48000c1201d150b80d500d084040b0b07480900040b003001d48104603007000c00e01c5866400d42220140556452885465000078101c0c0e800140702000e054003c2940c8043d8030300f411208040480070f090103071440c1703820a140200c44010f100d013819040e02c0040c61000585500007510040c40d03104080b89d0031403c1602001c1d507510391101d15092148280c0c00041480e08040c0600c844401060715240e048505001094a5010701e86602204660304d0880380000c1d6545c041d01b207242a259020001800300d0710318107006002000504401142c2c0c14043c4104058500000720f40407a5041402c0d02003c54516040c90781074030440e81c8a07a488440844901003070703d0007000600c910390000084642c51510300801c036003a50011034003c3c00ca03140041d400c00003400c2040800101c5446480c4c00c5050140e0f11001a0071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 840613875 1250 840612625 840612631
    0x9030d02070f02091321020a08131e03152703030c110309060f071b03051006080c0102070504021806040338060d11060a020a03080a060605071e0b 64
    0x2c1d142220400c0c4254144040010b401802a070880700b01d020b0541c076590744101c1103d080308030925002603055107562091010026807584125415504d040500720f0b4410300a29004940500d03d000910304030342c003001c0d4500000c60703902001840755420708410240003401c0c00201c4942c00d106c0d0b002180101742d143c120354090103109440c0052100c20136000101404035603d10220301f50700420000c041d0340e031400c0c16100b07030300c904042c8030380e860600b41340c50341c070101d42d00c24002a0304482001c04400c020011901c2d41d501400c0080c06c0180b2a0b68540565440034285803040c0540c10100c02072020341030039001410301031260022054481c00d410b02003403069010f0380c01540c0c0312006039400320004800b40042000c02185203550003110000c520b40d41c142c80380107400a0700c00c1039030b15046010004800ea1540e41d4007402002191901c07415000030f9195980454101c00095861000611650301c0d0303c07511341958801e039601c609280c002d03074903480c0303e10080c0c9402c0d01c0c51452580000004150ba000c0b00d04c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 840615125 1250 840613875 840613883
    0x1534081009200a0306050d060b03120403020f1201020c3004031e0f06020d021c0608070504020f041505041e12260d020a1e02030a0809030d0207 63
    0x101440e061200c0c03442000141c0000003a641024a0086035640b407440c510400003124400654800b48203400380e000f02196071041c0d0304440300d90034140030b001d00d0380c1c0501e103062000d4040d92030a90100c92031174124400e40c00000d504c10713800d03000300b400e07418102804c0400c00071010006107003012149941d490140400800000d54100405601241c144808403104a404140d10141030500f1580c0d03040304271a60a842d1940440a90091400d000108031448240c5821940031952418010580006580300c0c00c1080210b001c1c203581c00075002054498182121112000703000034500307000400000c1d601100301c0481103002400007081c00300c550440c02084114644440350740324a41400e00081200036812440640c4040030204250711820103040340e1071b64450500c03000c1d03100500c4080551303080c0c045c000c8690381c408078140842d0303142c07980108811b10940d00c5400d940c010241100261807441c1815100582060080c540ea060281b61603a820501400540f03041510159250040781c00144040c1c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 840616375 1250 840615125 840615137
    0x180c03190623031b19030602121e0c1902030408060f01180b010e040c110a0303020301170c030a0b130816030908031315031515030e1534 60
    0xc01e038600b0780d40580d1080842603019050000f00d00d140004980c9030030601ca0300070801c04444035104a59218480d01455100e5001c6480704443c10b20040d4a030340440e0380d140c1141290400c1e011180c000d044051003800401009407601c01b0143c4036610380c1d015800f0074402e520040c0000b0901b800300b0f01c0b040b44a081c001a00800540c586445022128140f48003070000501d4000c03051800c1c3d07070104641389912000d40307000c160000748000032140e01c0301250064510303000c2c90041d1020160b15030020350484280c0c500c0e1108491a08803810346840e0605c1c5e080d545030340504141c40024154240d5075a125480800d00e44040407a03803105449544001000003645004c0a03080041580107981c00b030180800100a41c10f03c000b22070000b031a10064011414440e44800b10320200394801d4002e0b4440075414056015419921030509081c001d2030f4801001003030070074a200243310000074072203c40fa030764543c3c0d134150b5845501d2800008c813028101050310321a100c0c170000840703140b2410301101c4440c5071364070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 840617625 1250 840616375 840616409
    0x3021626030915060604120209360d030c0203090918060106020604050106150c140304050a090e010f051017010617030901090512120906130602030a0e180c031906 71
    0x41a0403210080c100c5104800503c401c1c00516040a40380c160240d050380c107032030f0742d44440d00707030040e890718105039049108480c3d6440003107d07100100c54ac090100d03a0048400b94080044250181c44c4920a030100580c4140003135180c901e001c800d9281c01003122224400c43c0c0703488000c582d00b00f010980010002d80d01041c24042001024400c03200103000d04003110a1f101c0548100620100034608060a07004401d250380c402c204003441228000c1a008020352041603035084241c010b0900c1c0140c14480b0b5180040e044210a864021740348550b05101c5079070701e0700342000307141c070024020010007583c1e6650ba1f44010580c600450360301e00700c0c2c100400c0115218895440010400c0e8030940099001d240700b0409501481c400250001a000c05129025218103c010205180e401b07070440240c41d14407601c1c1e00282072030300800284080342c07407655114007003031a01007400110003140b07800d240100d600300d0004108849034009076400c59040804149000400c08120b81170703030f086400c0009258520303010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 840618875 1250 840617625 840617653
    0x705061f090504030503010b090a090501153c021203010f050916020d120908040308040f0e1501031e06090b0f030a081909030609050c0907030216260309 67
    0xa400c020120a4814040340c0f8065800501c0c070f00040c0700d1541d0300403010039900c00d9992038002180c080d0807400d10400040da0b4074962032856840c1da0303200c1404140b101804140020f07034031848603002c507071500000f440455100c00240d280b40700c401c216002c40c025600700000c90710180c0c00550091000b02070010360603007050208104c1c080003800c2800110749601046441e42d030003049003640301b00d5905242c0e120b20410310090b4054400100014120400000c0c08010000781c80041d00644000c010007200e09511140e9400c0c44603011b460b104c0040c2c02ca40c40c4075405612a410080ea0702400038014054060b66908140545102d33400283d1026280c5001c0030703113824910408450113600324000d041c08289900c030b0f1540c51080745611050004046d01586055010740600c1004540c8840c01b003240348000e08141d40c5801d007034032840d84100507440c04140c0e484e20030300035504182140780c0d030804115882d56540c0d00340f11840a054907803009170f0306e0844491503610040e51080d00308201414140c451320103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 840620125 1250 840618875 840618931
    0x3120711010509071a040824090a050c0d060e0a050a110301090b0604181703071e080a05070e04020c0609070b0f0315040b09010602010e06071e03050408070506 70
    0x9255a0035070725100c01c00100700d0300041d01c0011604d0001400c0b00e801117000e026900d030b10440d001003c0d9807244000d00030046021000518011941000c0c0102d00c0d205e103004251510000030024141368800b202000003454903400071520548100e0000070482c1d005841079080c01e0245c00c0c252026041002414144601c000f0051500202200200010000d82e034501920a2001d80400d00450780c980c04901011940c40b1581d01d1540c00c00a52410b1013100b4428451a0784211482c10018148942c0c64085912482110381200e01549862281c0e545600b8110005c01d401000081001000340c003420144e12680b000705440c0604001600c1a4500030301814980030f100d500405100d10304001c1450a0641d040540c5c3d0440040e00c960b4416201c0800058043d0610000303455004001070000215141c05602600c030726144e8a00b915941d40c0c803040c0c00c0e41c0c1842c465101c0510004014080c0340b42c0b9109511407035109100b04841c42c14541a611900c0c60314001304c50312416051074001d40340c58030300015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 840621375 1250 840620125 840620147
    0xf0b13140f1018080f0403061d0115060804060f110301091a0a08330f0a0506040e07050411040f0b040611010603030512040f0f030305060f010908060f040311031207 72
    0x2041070052041d4035412902c6803c03a4000a00f03070501c0468291226a21802110011174101100340092400ca04d0a0342d042c0a02e40c90190056192005c90090075441d072044800301c6084d600c60701c02c01e0740c41c0c0e290907014003480300f1076080580d512020150745100003000f440c041c007010f0300001201c9035181c1a8031500220040307060311072551440708001103c00018031011380c0c0c2000524480d50f00a00c0b0500100484e030540104960003050b08000d42501c60103200c605c540c091660510080d150401072004641d4102c44d1284d40e60441081404181415000305204217070003a030452400356100c40802000d0b500360800408100001010407010354841e0011002c040303818000c004007459130350090600c1c4103210070200c140041d00300050071720440340074021500f500301e20402400c44152800400505080312094032500540f9011415544500d11020079a02420001c290301e4803908070854018000078000c40801148110b6400464014405400b1500d011110440302d03041c4100c01070f00441c044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 840622625 1250 840621375 840621403
    0x3060f03031209141c0809030307140c0a051005010b03060f1e06030f01050108181f06230901140306042d0c050f0904031b03020106210b010807030f0b13140f 69
    0x14140003107c0008000c5a41155403030602c10200404400d0f076006031302481100742e025001d881400d000703005001c1410069101c01400c03c004c4c40ea00c0c0c1d00c0007030f4640402e40b07080c1d40100d0b05219007400c500341034003011180c1c08484202c241c0079095100144c45580b04407080000c0c07100c500010405035800c218040c1c3c20803e91034540e102c0c43c2c0c40d454003980e5400491440c6521900b04041c580c0343c03503516408030024010315288410f140d05070b49028031703482d404800114090b1004600000b01d03444168103800302441c0040262019481702d803101d14aa69843c410342070403265411001000608100c01c3e1000240315000a26180b4905400c100030181512403103806a140c1c48100400698010321031030248040008440790700001c0d00b0304070f004080d150043d200b0b4000520103003031000c2440840038030f154410344082449a8840c404e90b034584000d07102c01044840c50712021070008062011813030307024084102801040b480c0d03807a010101460b04080492581060700035402e5600c080c0403c1c1a00900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 840623875 1250 840622625 840622637
    0x20f07090902030f0a0302120d23250906050706062606070314070305040f14030409051e010b0a0e030618010f0c0905010f05041d061003060f03031209141c 68
    0x70300c2d1400b07502c80a08e40210000360200007405c0318007a601e81d20058640e540800c400c030100142041d03d402080094a0541166071030058000c5801c1c1044207806440c1030596404000d03601d411029100c47d0000a0101c50311a1203100100f42100300c41e4044d403a014680c0800b00b1742204040d1f00324103045007c1d04580400d8184208618094070b80700900f900712455203000601d41c1d4650501c03402860000c1802040c1d604851031690701d241000000c0c4c016541002c0381040981c50b1421002c1c94a244107424120404c4103000400c00d2907803540192205075210704000311480e44c0d8000007410000221039000c4003070014030040108400034400c3c0c0300400181c9400300300e9521140806010310000f482428104026070841803203840c8030f0800d4800a05030741d440310401c2c669000842440b06004c0740c1c00c6004200302a40f107507210f4400d0041c5011640c19981c80843c00e030860b101200c112003440900c210060301da094a0300025221041c030316074504010050481062142d1404404c4040e0810100800103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 840625125 1250 840623875 840623893
    0x5010209030109050d320f070605070f030b063a090305040f17060103080306130e0705030d3b10031e02070302190c030209040b060102070e0c0a0f020f07090902030f 72
    0x4594401041c60000300306c0840e05c079030441048403818420361200074035481c00e10040c000041d421544000c840e503c43d440a200100e042c60500030345002d00d0040044070010620020150001072001d19903c032003c5901a108480300301542054810036403088000075400030342000b000c840301c56400040d140c7c4030f41110070210a49003003072761000103004c060720202002000c901e16030345920b40700d01482c844010500070024941149500c1d60020311a5a009015000490404904c02d203501c0b07501d030604880d11b6140e614508042c49422070200c08034100e01e400c0c6040e0300c0c907030f0b9030300b16400191000c150ba01040c0d9000140c2080034001850061415a80c0180036150000e6008556001c600308410044102c60a0b11300306104400b50b0f40c1e04c081c0d040042c45003803100303001003a244036200d210281c00701c42001d0740d00c040b441c01e40c01048900c016810130074011810014400e4140784c01030007891040f140006400d5003854180030103680030b00c1109030340e2032020301142014410040740d50380381405010101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 840626375 1250 840625125 840625187
    0x8070e150d0507091e080c0103020f1801021204080c0307050f0609010305040602040b0301120b06010203250203071503020c010b0d030e0105160507120311060411010c05010209030109050d 82
    0x1000da500c0d075074107803512040010f140502c00c0002000800465109000000c1e200d260b00d00640c2503030280d20396502510200c0300440d4041d000316150640c89096103490a9010404440000318600440c0d04601508040a4441091401820141c6102d00240030aa40003200700341c81d00c4040d901203402100c1d0701c43e8201c42c950b44c0c80d05607070740c2c50030a00303002c101d5950701d203080c000a20890b0001c4c50b81e03140110000c510301c022080c85001d864400e2800368140e441e42c10040e6505d000e00a28250130b502c2d40c2d0318070b1442019081d0b081c14600d1024084595031074903080840040700700303091a100042d50104061480c610240589520b412040c0c6d03010202103219100107200180304003c0e00d06004001440c4008421420b1003504a99000300550f52003941b01c41315150f5140c2250402d80020300d0440105d2004480072600d80d000b00e90000c0000c400400040054410183d503950543d8107540c00d012000c541c0c0c07002c2c02074030314062003000035011101c0e40741c40180c1002801802c0303030501842c0001d039004c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 840627625 1250 840626375 840626377
    0x605090f1b1602060c0a1b03020d060c03090f060507090b0711271311041811040212090a12020f030405061b030a0309050c04091a06040e0303040308070e15 68
    0x401e5480c0000d50301d1441c05034108111001440094000000044540400c0070101d41c0e6000107218100c0355034802c0303080e0202a198006400003951208184072840c00207041584050350304400c5040221319181c5541b40c5a103e0701d900d8a0980341c10740c9680400003030320307070044559010700780d2004040e0500780700380c41e810101b8149a007914042c0680c65200e6515800100101d03110b8103000e400d9103a1460300103001103998003c1c800850301308480c2c00c01e800c45403074203000300c0d56003203860803c4440d6104940c464100c1c0c99540740c21550082e50801030000da1104030181c5d54407401c10703100140411b0505141c0400500c180c6000f9a045402030000140400703c08000c40d0b0450f003088a4854503500010f8032003030042a2100141203910000507403809040d0141c0003407503554000e0060f1211490014140419503030b80c010010188401035541910014243c141d46420030000380000a4160600c602c191031980140c600713601050881003000724407135004401c00d40404086e185d1840e410048440703401c607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 840628875 1250 840627625 840627661
    0x5070c060e0c0307150e040c02120a02030405040c090e04062c070e071701030f0c23040b0316090f0e0607080f0601031b0804330b040203010605040515040b0304060605090f 75
    0x8501d895108008c0354a10800c41c1c98403041d03400811503950f10b4909406960b03680a841158010b60410b001411003a00410078081169202d41c07502046540e1640d500c0300504686401d0580820f440300c043c01d401c14001d0622241944010091030b0460400d140013002e00070082000c000c0209440f500641c4d411101d00b1141100e80c00100e08410800d14500740300b00010f643c00250170580071440300d03114480700300b03240000000c00b80d40802c090300c40b0000345a00c508071903085000394606180200070200455000b210311030220076000418000e418141030800c50160780c0302001610610030301002640b50b0203095000702090074100101c07181c01842100d10811034080906100d02c6800160501089405031404001592801d80c41d290780301c1c031040d6140181143c20b601c0507107009400c8549090070310803039040e41ca86840b0a0b04051800703081003d0b845a00800e003660113000d200010380d013140310000d18011441036002040c014208000c1c0411f401d0014080030800d0114000c1c031502c1c1c0501c42260358 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 840630125 1250 840628875 840628879
    0x50604030210020a0206130e090a080313030509040204030f022107030809011b050715081302041d070608010317090d0204150f0f031110020d0305070c060e0c0307150e 73
    0x2c00d400ca2030400e130b0902074139181c0030703400510001c0d1280d4500011440d00d010386107440070503260394541c8080c10f507076a4881140201640c000b08041821030b000c00529045aa20a19186190160080224080c0e8016a00c2154a0024052902c00318589200014100050142c2c0d403c0500d01215449580d46420b05c0007800c03072039001400d086140d00c40c0107a810401090703408030210340903174540f081ea20020340c03069803031100081030401c442c14850030800c0d0159403201e5018030f6800c6d05400700001491049603070070080031490480803486105000d020300810807a200c0c500740798554244031a0b25606d00c203400d00e042d0003c00112605513591120491410f40580d0002004410740b01c400790b103455181c21004840b440884c00280d00d9451100c240c042e0381c03050507040e954000d030405000d103005425030700e6000b6070403164043d0441803081c1d008660000c5c0c04d10344035052118540b1040225000c180c03070850350307810200405010b801c080001c0c0d001001907030304002d414110071000420b2410350360b05082c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 840631375 1250 840630125 840630139
    0x406030b0f1b07110a0803180103150f0e090715050c120406120506040626070e0403140d02161a0105090c090d0812091011070c031b1802070b010e010506040302 70
    0x64050340b038000c1c03244003410b0b003035088a60322310742d00884141d030118400c440340c00682450386036000032490b00807500403548020125480c80d17080850442c0d00c244010040701e1a84100740c400034400e004015a180390a4184c2c4079944d076108151880307070811000d41c0292200c2d0004100400c1f0107036100000090f103500c03502000980f61141400100644150340c0400e126950907107100a460721460300b1580440800da04844a2560307519884042c07070000c89002c0c02041d0698046800702140900400c0050340081c00145402c0320b542c10362152200707181058409602e00c400d0310801d0340460380100d01408045811065528005000d6600391160448081c00b0342e148000240c104500c15050b1074a07406494160310b003618161841943d00c0c00311459401100303080c42000340f07031076000101300e50b4426003000500c1c403506e08586079640707190040d04081c034680402002c00109044000c1c3e5207080d0200a441c0903a49034400c0c103100917032500c107802020844021400400c5a40e44001c01c440c22030f98151001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 840632625 1250 840631375 840631403
    0xb03150909011401062d1428050d0c180b13050a060c1217072609010510170c01110321100801091109060a050406030b0f1b07 55
    0x19800f401103144800c610398000c0b0008a045504002d80158040b42c100703c0c0906d07440440c14540c5100d0341c01c110600414507003805d841c034a444940003402c2008030072140d055440032402825001001587c248000200c0200d40c0081151480c040c480208034585440c0d01504295117050503d686684a00b4036190000901c070507903003a800300d4000c001d02009180080c007903914403000c0c0034510002011a0a040005481c0701054080d1844500c084071482114031150b42d80841a112555882c1103d28161a615094031a10140305c0000b44070340c2035000007155030704203c040800002c0c1c2c650001c081c0502c4038144c4581d04a4001808200f22101746091a40103000c02c80050440c880c4505900720140458060050a80d00144440c09244409010301d020b40e940d080460807a429540b000f00900485582c4c0303036070b6141821007140c01000040503180707017642d210b0004085070026402250300c08144001c120142030080845544503085056074603010007903010014040c4a80e0720000c201c41210280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 840633875 1250 840632625 840632641
    0x140409111002160f06020c09040302151003060e011e0b0607020405070e03030d090b0a0c080a0f1e1401080c0904140304052e0e030c09060f091f0b031509 67
    0x2d01e0b40c110038180320f41070105480302d0344450b10400c1c50041700c001d485400700085c210701300329901a01c1a0b8065005e031070300200302002035402c40b6000c0c11840f00f000e0100c0d00132012030103621542d804040008000614150a0511903282ea0710103409241785a1800d520784d03407251100d00c1180c82c1554100d90005065846103000c0d107907040c140c5100c680610000c11020035030703082940880304885c001d4251410a545044a9030269030b20350320300200003503060010920032045030700601e10031120890b0105119100e4011245000d03c6500860081515542c5000c4192040640701d0f0140085002170140303042070030b001c00c00305200504002c102905203010001d00d02000d00689010380001070111000140d41d1010810b40001042025041c440d455903219110303025500740310340c528000d0b01030180011030008000000d00d00078245070b04241250400c04040d541c8607c00e500c240344180b90302c6c100b29031742140015031a00ea40c00104c5000c1c000c01c2400318607200c0303500d0075031104401c4a035000d1a994140c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 840635125 1250 840633875 840633883
    0x130c17130501142a071202100f0212010909031b060b0901030624030c270f02031e0723070c080f120405100f0522140409111002 56
    0x11000d445540707080c2900b9a000e54040c0200d008504c000080203090b0658043d41071520031091001401c4c103810028240010312111142c94152003030700543c5c26504d104101c4c41d003a140702c52000300140740d0004880a402c1c20759440580500300743e1100300b0030034075a0b9801421f120203d26111802a00b140103080030064950040104890040c041c82e11550390b034500000174011baa001800c103e002c45020000843da0f41030268200e030b81200c00124058038100b84d40d0300201c01e070340020064659461501070aa21203000b1080c1c018041000107941c0d1400c02c801c41c9500441e03445003402c00704100184950b02d070f48080e081e00c00d000e511500780400f000140d11080903100710400240880301050f400102c1000100d0013001107800181a5050381c07241c80c19842d032511580c000c1e56404a111900720705540c0c429070110740001d16a0800740d2420203d000d03950300141061074480d030780c901201814046071a4107a14800081019201884442125a195001140501ca51502a2100070011180284208 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 840636375 1250 840635125 840635161
    0x409020a090905010b0a05010e01120222030c030311123703060e09070e0408090a120b090d03050f0a270c080607090b0d0e0102070c09050402130c17 65
    0x303204228409203440c3c0503018181840807148a90586680003402d54040c100900c2d607948140e440c1100607041400081c0250085130328515004829042603100001000ca01c1d009140925080030b000c614524000703014400122001e040c1d6000850003480004450041c0c41d0404444104030344e00c100703000b0312100400100b120340910000940303d41c2410b01c1d0598045801d5a0960702d58030081e5803280d4000350b4540c000d20988415249150015006c0f5660700701500780b01c2c000400e900f060550300d03001d18941e240c0228059803050407440500080020800c14228182c0705030406101c40c1c48c00d00d04540b08400010030390304040d9252500980044502115400305080d100c1c5480c0c103a00d03c6040450101c042c0d40240041803242d140440e0b07049020344540c10481e0150003c10f454032040c3d41c1c210380a0465202032106d259007d008040020b1540015540a085c0688002411b460b01d80100121011a0288250100d01d80a25003000c564004801c5035407040f07080318a0619103c414940d231240c3e4a04c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 840637625 1250 840636375 840636389
    0x2040e070c17040308070209060103020903030702040f06031a0106030507090312031a060f132114030904020720040e2d100903080a05070f11010207120905100507020d020409020a 78
    0x14004c0208140640030703150301402616025034680d1083d006500700d101d5503075010341c075501c2030010400516064002c81c600484803a00032070041e550b40e60f0350301100d501e59841c40f100e04682005014142d8180300ba5035000e0003d1030034080d0103241d500c5442203201c618900340101900d0b0349a20600c010390603540d00d1071800140c000c42d650154940380c4030b880c2d00b180800070640311054100244e0000e040e005640d1132141503031050321201c8140d48914108000e201040c05c1400180501480c540d128400391013000d00940754001e042d030b0b4004e010001081d10403403c0d4803561608a4201d081e15001541055182040d40d11240c40031006940c92035030701e0695500e0489124031807200c1d8000c40b007074000c3d803580c0d40329440300071803a11840d44420075100c04841407000030700d10303007007003400a0302c500018120030703d8440c0010700c1e01c00644c5410651100740420300c0c0c041030340701008001c5410420703005080100a490040d040911680c0050822a4400b5001c1d01c04d9480702d24602c25983c9980c46003000b4808 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 840638875 1250 840637625 840637627
    0x4020f120a0606020f0a08220306020c03040e0c1207030c020c030318090f041707170d0c11010603110d060605030f07050406050405010e06010311042c010902040e070c17 74
    0x7040c070300e04010708228090680180550880d00301000400551845955841804035003444941c2118443c0128030113404a241c0c64032180001c04a90b941c40180340003204100030310755403410300300c1c1e01e00082c0c400703004080c05000030404104101c3c440c1e5011038002440b8500480d40382d4100764121b2511400c0b820b1243c0c10f00000030303030409070b44440f51441e100c60415201480940d0300e0002c2c15000003402c48019104e5080f10460480110100d0003c0580c0391146e062508200c0040d070b40b054194102419001c4c0007030791303600765048540d001a07071704242c1d0a50b04000c1c081c60b4255511a4824400140c1c0c960107003081089208c00c001d520b401000140c0005001ca070403402c80140201c2d902c690300e11555004914152010982d410140152070698000c10a000c5042e260391004500820460407010f503403e0042c4008200140510703140107101c8800c40c0700d19100c43c841c580c0441c0e0000107034840204c00348100710030021304084040f5507034081c2c56414800451902424442011559820700c001c482d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 840640125 1250 840638875 840638881
    0x90f0409050c1513210305030c2521022a0904050d080109110a0507170a0302070204111204080a1119060b040902030c0d0c09050a05040203190b01030204020f12 70
    0x1d0b1401800d030a44004d46000c010594a40301024101c185052010b03186106244e200e020070700402c000c64028154600e864a00b840c00c22400702620203868040c5000141c1d0400e600c1405100300fa41d049046001118098400e00d07610060369038005841101601c4481091038101c00d11070f10f41c42c40a1402c06481d122780c0e803900e03180032a01d640400c030413080456100c0c4004540e040346031082d504c40c2c81c10b00d2001454991511400d540507040030340c00301d4560741d403c2c00d1040400d901034050125000070307031000360300c5224600c100030a440e00f0b41c069a410703ca0501161058620205410350400d410490180d0307100603610040318465450240e11f107140c400d006101c6550441c0c00c00b101c1c0c086001d10000c10200008034100000e8890250300a54142d010208450140c5880c124100c0210b2003801861400b0360b8840412064a400b1a407500c0b04035942d004004c1507003014440b02c1e2256941150b0558002555990405009410b000280c02203502040b0503601032075003070403600c0680303045041c508545 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 840641375 1250 840640125 840640159
    0x6020c0a020909070810020d090c081617060a020715020408071715070806040b0d080d060b030108070b0304032a020a080c09010b0705010626070506090f0409050c 71
    0x1888003101203026020303120004507a5280810b00c401a24180d4010340645650309444601a402407000001005d55900d034a1000800340c414440046c11745201500460703503041c4001000c505140e004074048036130321014a03000000411681d034050910600145c5440183c02c002b480c542206c00c034a20210700c0085c01140910f00085c05000b1669021980c8246c0c0759600100c0e0b031100c0c5001c0000441290030004a00e040b80610256a80504094400100c0503d4140016405011404280c1d11410002500d9000001c5401004042d085010200c2e10b15490144115543e00062040045900300400403d0425100c3e01c5494580442c08045442000342c0841c1807a01544808080b845965a44400562903101140b50082144000c0500f070040e8a8100402001c0c1d01c1581d0072942c1e950394001c0411040180f161200c01103101c200042d0f0bc4020304580149001040e400c5244240030510804607030395604100d41640d403600351004603d406481ca440d610b0302480a60507981b02080c544280515 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 840642625 1250 840641375 840641383
    0xa03120903050706240f0302090a1a041e0c090e1003120807052a150115080a0e0d02070612091211120f09011b0305040b0a0e04050c0d0c080c041503020706020c 70
    0x11f80d00848241311a52501c6108000316401000e6000222810b1803e07521585010340c0030000d02d91031034290030500c2a07001103480407241d4440c8410b0115408810a00400b2030303185139254071038070340b05014400f5400c585510a0014680e94030b1000c02c0420000940b03400d02c28000d95042503882054585801c544091115806070107031946a00c45c86036103010804d4264041d047d0b41200c601070000c000080c1d0800086500b590001e00f11120503407680c6100041c1d00041000b0401d4151544c00741860a0074030000820082c0c0c100c40710340704a030800c1c2940c07001c2072100d42c160041048904000ca03845200044090504401d41c0028001501c00b051003888161388a0041c134500100b42d07900d6205840311805860f68628051010300000c009000601400c3e80a40c000e06050320350703080400d014106a0005801c0d0b4500301c0b00750100800c049550784c200001406656224106428100b0140c1707401d01040059001d948503011141d02000904032500d4025411140c105030060415951071284010241c1c0e9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 840643875 1250 840642625 840642629
    0x3010b0313021f1704150f020f070f151a01030228051b070e06040203040503070c030804181a060a1101060306091e030c060213080d020a03120903050706240f 69
    0xb040015062054401c1104e09451040e940044101548002010203200402c410007882c01515406c00c8801d20303035101c5202502c2c90502c2100740c8040b003041803030456440f001203030300351440c542403075218001070420b80400d00c2d403000c081c40c0040c0c44009910750851a05450729283c01c007020001c101c0c00310135610030000c01c0c00d1141094202d00c00c400200307109075100101d1103003244619020010544914080c1c00460b041801601120b0500c0c0040d00d501d0b142c0c0240d82d000300c40c1c0940000b4104025050300c0446070035810101000c002c41070744800e0840d0000910a81540300e94000120045854000d400001300620140003c000072500c0c1e203005c41c010b001c001c40640f00280c50481d0b10400344184003500320300030781c55503e0740304000701944e4980186d0020001c250380782e01403810116880b01d0400280151483c543d006091040c8581005480c05c121000c08124003400c02040c500400c0e004022141c1040d4801000511900c00d810380d4012284420340c0c160303d501c022800041c44084d400d4101302 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 840645125 1250 840643875 840643877
    0xe011d1b0f040c2d050301050d08090315090d030605090f060109170303011a090102100e01061a181905120f01022703010506130b1503160e030601060503010b0313021f 73
    0xe800c00000c01c40200200900e03010344e00040041005010341e00b80984021b030203030b116065079410b242c0c580d000242850b481646200c41d046804d001c020f06414100b04a148032246410204001800c000101d040c0d944000c000f140400c24030720124a06900c01c0001d0402020762120180e138000c01d80d221503890760300038814980c0600c0041c500c0c41401d108141101c4080005170020700010043c00054400342149513000c84d11035588050020300070b0030403602c00c40740001c10b040e00d5551340c100003201e209422540802c40c7c01007082c4040c401121400c4040002034990480c0c2144000040c240b18074600645032204031b56131350002c070b0034655589481c6080c121164001e940d62207802440020f041c2220700031101d8035400702c000130720f101081030658800b0852640140c40b01405203e1b142c4900c01550040c0c54038948042220014207510768070080e00d0f8041c2108501601c010352404100038103a00040c01020300600c03000012804200b00c0b540c600110a13806060100b88201181c101107092061941d070700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 840646375 1250 840645125 840645167
    0x90c15030108060f0405150f07110a120e0406030c0e0609011505180612070908010b18041e05121207050c0a080c0a06050a0e011d1b0f040c 61
    0x14104800401524181d40c1108018181582d580c0c1c2201402d940281c4281d905000c1c90540c6000c4401c000d40e040d200362607005513058a41450a001400034200d03003804201c6400202c942c0002504041d00501072080600d0f1100301e89000c3d00c001402003400303910051851421050004800404601003445241d040f20b41c1050f0384e1340c644c1c080b2294000061a41e000880403c04618030444010b019509040c020300b00078101603441f100509003081c1580d0314000305c2c1a00b602002200d03004d00560151110035900b03041c10405903a040302c0c41000180c0700800808954014070500001c00707002281c40c82c0c0001c102c075011480700f00b000500354080e80360301c0701d40f0401c440002d4096014a04440440103d40c0041405420755203c2c09515004403502507101d01903422410007184641c000c103130180004e2140011112103000c001e07030031103900825481100562098880c0841004518160044025031100c0c00000700040028144401d1200d9070394041c0c500f40c4c103103d442d903202c003125490711906c401031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 840647482 1107 840646375 840646399
    0x10062703122105061201020c070b1605031206090105040603051e010b0406031406010608060904151b020d18230a090903020312010b070c1401021005090c 67
    0x82c001401c3e1100140049442d01280141e034a441d001c00851808140f00c18140e110b034014412051000808100c0c03007400030100c004003070036540c403405a0343d4904d080380b209000141d06172400c2e402008a50300110703441c00c003440b80a0550f034000c802810102c41542214140c1081c039040380c502c81d520359200c0c580303540322402440041c500c201a449400900c41010a240420591116081090160911103035846d094001500680c10064000b442a188070001c001340c00a0288000100d03086180350703e2203540403d4402c000c40c0f02d9541c02a40060907060b0306400c06c103600902582e80750408080120701c02c040100f12441c00c0192552444564406041d022642034542c2034000d6000040ca24040385003c05140d400f40003228012810001d0720b49811101075014001d41c8500940203000700c0d0581c0c000c12800040c041051800d00482c9000b003a403d844080807108203004921000340c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 840467625 840647482 := by
  have h0 := BRFrame.cov_init 840467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 840467625 ≤ n) (h2 : n < 840647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
