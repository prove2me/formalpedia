-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:55.484986+00:00
-- url     : https://prove2.me/submissions/92ee8dab-0a90-495b-ad49-321179dcce84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 917266187 ≤ n < 917446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 917267437 1250 917266187 917266193
    0x603020705070603091a0a020f030a020703090503012009030118030c0b06060405180604060312090302010e040b102001151701110a0f0212070f021816050f16 69
    0x5060100d01c2801660481c90b22040214112268030b24007410200500c200780607005505840d141d00000c0108002d807420340c10900324419680300b500c03d03da0700fa500095030010f06500c110b0040c041e200c11402030091901201c240780141d100403201803000d4200161070306150340c003503000500038007006525042c10045824040c0c500341540d8402d940030030802000840c07074903000c0c00716429110b00030310032400c65900d14002040700c1d1001b000c140c0c000b5902c1c440400460341148a0080d0511240d0390040c2c55400c610004103011001c61045000e10f007070071410070403035480400c29003005910b07140090680d2442046045c00354a101c01c0900780b075103040085000c20301d03e2400340c0c055500e09106100c00201070f02815080320206031960900d000305110f00302540e4403801c6400c2e01510340344126200081c14007051b0b5507a60156a0485020001e011104114140041c000c3c820902400e6000003604d410300e000c0e45280e60341d680003400c2150000b014100b8242c40025104543d0480d210705410095901d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 917268687 1250 917267437 917267441
    0x3030a120906110301030b0f010e04030507020409140303101406090f030703060f0510080c1305101d07021e1c0507050102031e0907030f0807140609030a091706041106090a0603 77
    0x800b040d11401f2522000448205412514074120744114242c100d25650303544003110540c0008904981c0b00e070700d404485000c5491010351715400d150a6000d140d0b80d0800c03010b060f071103802e0b5920070702c1c0044030034003500c03000e648280c16a00f42501c29650390320001c00030b40003c2e043c0b100c103805c0204030f6894454288001000c980c06107214a071603410030300645840d8a00f243d60350f542c1004603039000c445160042404000c54014a42143c40000d00d141219118802c1c0c6418280550f00c807141410700c3d604100049a0400a15014807202c003014806140c42105240c1c4620401513115040c0e504075600842051094044401c0c545d007006c002c64590500f12100304015411f0203281c480740885001041d443e500104aa00440b40e02505903040f00e4896601c0c68607035080198182c490a0415007030115031003007400903034071980c00d04025566400d480c0394054101422a002100102a91880320740300000c00a0010741050f00400314100c507200b4080010018880c103894150400402000020031075099 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 917269937 1250 917268687 917268689
    0x1030911240a02030c0628112a1903080f1b0a020115090614010e031507080103030f02030a0801053109210206010b0c10050708160e03030a120906110301 67
    0x2d0a890550701c400340e4141c0e445211f030005802e00d07410715820380f40764181135101140605c400181c9608298210098010160204880803420001006000112201406a950f00c02c464800070311045466440041c4038400c02804c480c3c552110601181d280c510845195003440201242c0b00c2d51807030b100000034080c0480b0f003045500c25488050100f9141703c0c07402040281d030b4002800b448034042c5503004549000c1c186018030380501815003076024501c1011f00051140d400740d110100654514a0000d08c03184101750340604641080c000d03280680d6000030804d04442e003c94005041c45205004c0c0f504507035840c0303e040c50660090707201c60300140141c2c0010914500401496610325100124012015110030014005800c641c00602402e0303005805080c410b014201140c8038007501d691143d003252815204603000c507052000300403100c501058000c8080d52140381442c50f407142d01c40400e81d40e0044000c0c0d1820720201d2170240150340c04641c00400c00b1500001d003801501c12243e00d840e01c0c1d41c42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 917271187 1250 917269937 917269957
    0x31f050a0906090b0d03051e0d180308091501030605071725090b030a020f070605090c10030c020a110303070c1e050316050d290603060601030911240a0203 68
    0x184000310815117400f000e640e01c1c1a41544581c2d1620a0046080079012003446810034290070900509005014501c0b0741c04d210702c65866628110206414003810800c4000c001d08001d50092500810003054100d0281c1101d522030800300c0c19856541080d12881c60303014160303001d00c0b441801c20000c8213017011160191407031883c10411541190201310380c40c81c418060215110003c00200784611101c3d8020801c1407142c600141c10014695240010b4481c161844106507104c05500b02442c0352111503601c0f20b203028101000608099038020f5281d0700b217030384058050410205450f0082e20300b84104c80e400356004080300c860948460f80031507003118081d449502c207800c0324030102d16410009505078403070f0303090011040510310700307810045030140e04c40c0100e13201c07490141c0701140b01c5902e0a8203204003003d210102124500311052610f000f400620041c10541864a440c010078500d9078500001f01042d03503c0b0706645101e02c141c46040001c2e52245404090004030b84600030b40c00f001506401207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 917272437 1250 917271187 917271191
    0xb1b0a0206070e1206010b0904020403080c0606190e0f0403032c06012c100302061c0e06010f050d0218190c051201060f030f0c0c020a1505031f050a090609 68
    0x4600c18404c0140c913028804540fa40004010301c010f4001070058102a6001040580340c01e440395030b4040141c00c080e0218180703030700c880309000c42450b1004040c00034007510b8514181c020b00d0861880b2407108060590340c1070442e1400030506161081d01310b10550407642208011000c0401c040c04070b180c62005117043c1d40d01522002240003201c070100280e2491005810040e5441542942501c4060141400c80400005280080140c86240c050a804581903500a50420b40f60442c8400e80351520208517498101c10b00501032401048154006c2d03400a58051045078501c1c400b0404e00f442810700c454031680e196040007442e070003142150b0034268010b40c1c240300c0300350f9810099032139008840d900c5445075850001484010312842911010030f229240c0840e40c020000341d204220b076003030300c030140014031880132036000d6080540020b0000c0c01d040910381c2003c078804000403c1404007070450024030341c1e103018508541c859800800c02034000248941c1800d5600e980d5400113003114803800e10042c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 917273687 1250 917272437 917272457
    0x8090120040303352a03011707060f030b04090212010b0102122104060f060602010501060216080a020103090507080f0d11010513082b090c210b1b0a020607 68
    0x505124541060800340c010004004c030b503150400d010010003c0441100045451140c1725a9407104440d1741c00c078a43c828655a20350510210110042c54401d5034a816888404100940c56000b4402d0a41144a00d800900e40c1040c0c0c1c0001d000d002c03651006507010528414041d522181940300d5103401c0000d13000c440d907001c2000b0b1844994010414001c0c040c119006c001002e0110802e092603100e881f81704001150907141404400300e900b00c0d00011b0040c0e642d01c005106480d0100641c1c254411010b402c2d110842c03905120603a90451524000e04168484a4040401c0010006500a000000282c1c0e5217840440d070400d6640c00c02c0001480042c2d82e0761a68000d81d10b06100b9a8015a100302160006601c251101103295021a8021076406d201003001c041849000706c14482010410f040490a0049070030031150000b0305800c070f01d06000c08864031003a585403520072640c4890303010036160302d950b0710a00240c64900306452103400c1c4800025030965482d03401310300c00c0d205110603110140b580b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 917274937 1250 917273687 917273717
    0x1230a022109031501030f0f02060d050f060f010c0506130203010b09070507030e04090b0a1e14010e0f0c03011a070c0b130602010509100f15060c11040c0f08090120040303 75
    0x1000a202c007421002040340304101048d6120050114a4006000d0610341104d000c94001204e608689072100741e82008184082483c0c108403880c0044024070303000c9200501c42e1102c644804002d002c5944c0007440c0c80f40b402c11034500b9003100317140f0440140005c14528054a0140440d070100348200c00003050a1807091451810b441000d00007504400c180310282d4660400700000e00480c1803280d54045040b8100e1001c28007070081019001804040011552500d08220716429014024444158001d400c0001d241440c405682c11600502d90386001d1140300d00c20b140880c818500043c01907031381800049031f02104280200307891520400700a01d403075038a400890895805a0380142950401c04880b240283c0c5500700604501e0f013248000f480c601d00c0b8181c408a4038496206502003106d040d03483d4107000130010380c1c1301d15010644050042c082c80b00c0f0028480201c410000b000d0041d1800413450812096000625000082150076603442480d000c8080b6500184021070000303002205032841 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 917276187 1250 917274937 917274973
    0x1e031b0e010504150e07090806010f0303110d0c030804031403010603020c0c2b05030417010c0807030b03060c0315130e0d02190209060105160f060b01230a02210903 72
    0x1a0700815403c400545d0802c0e524a20101340a000b42080104001003c503825009010950003400d00140314640d80e0700d50b28010b4441005c007a0880b81503040002107a01c442c1e0006400c1a0003940b518111fa100d50395450b01b500c508460350f01003130310382c003011002044181d0558000c1181040c3d50048a0740c4030107200c2040407078185034201c0c0c181810301062048030483c2c0060031b114154841c0b81540e0605807035941450344440e1203101d107000e0307039122800014041e8000c01090b403c5499841e05104400a000110790345600c007400110403074000200050800843d0210f078284610028000502007c0d00502c88014000030607100e10319020b4150020082c0740001611070b489001c914003403100325620b4003085148400100b80505002082055401070003070480c11b80c80f468818000803900348200d060607811182400e0a441c14004040d03440e21803881e0150ba024508225001c070681d9a18241108038244121500001d003501d0741c0100029610030307000083c00f50240e095045031a6050383e482c9840b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 917277437 1250 917276187 917276201
    0xc09090604110108070306030209160305130f020d0804090e2505010c0822231c060b031e011b0807050403030311131511060606041e031b0e010504 64
    0x4020305a5010b070304035401621081c3d032000180c00c00145e01c50f0340307801040d40c981049403254000e05803440341d000b416405204143d04107135072003445844500c2643d645500940c80c41d030b01074420300014131075100300a00c3e8801c550240c24007400c00c0c40040e03817008506030703642007042409104603c20703100406003a1141513590111001655140c3c81b106607500c0348000755010181646135946400410b1030715280c0711ba40c0d4001000041c4840c103900c0c3c4000c2d4465503444448560034401c0180b0001161003240c0302c44603142c01038200200050449014000902d480221032907c21110b00c10000304540c200198410f21000301c60258070408440c0420007211803107403c64901000c120240030030f10200b1b20a60000848005041c101850b18500c002180c100000e40e0380714914040e00c092594010650221020300068480d40090145007040c0000401d18043d500512041b8041003d0065190904040d02c80c0199045050300b18004210324003241150294001e0780d1903104460000181418a485088 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 917278687 1250 917277437 917277443
    0x4150e0c130e01021605070909080912010905070b0a1101091e0512042606010b0d0903050d050f01150c0807060b0402131e0b130e04030507080406020c09090604 70
    0x3015205820810295940718104000007594545520a0300a0301344010000c0d5107000d140e102c2c80e83d00600d000c500d00301c019040002c00a081880b004005203891040e03c5c05e0709002c031940c0e801981c1111030280105140c25003d081b034401d14500090420f0000028504440d55540e001c422408202580d8280d40d54040018031070440d0743d9108102c0905620400c0929200d101074036901c41c1c0e04100c070007280c0c11680241414003100d20080301140c0104040e00c1070118080060012503141102020320340c00350480303102d0301c0343d21500848105445181140c48044015030100503d0a0507448540c5d000001d01800240d040c0042c03140340660300501e40403030801d5000740f505113084d02d903542d40c1c40a092015891500b080d000e010400b18444440405009003692171901c805c0701a000800210420040d0f0102d000041c08021036100c20074402106001d54240300c0083ca0152294a01118a03100e8024050540c4d500410089500e6030b021035400f44c60a412580140140ca5810b0000c0d21900c040d1001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 917279937 1250 917278687 917278693
    0x301050901031113090c06120b0d030509011101050406091a1b160203030a0309120f020a02040506032505040c050f0901200d02010510120201090b03190e010504150e 72
    0x100005a0324501e4402c0b03120f4064580009000c04880c100240da600102c21100f1050302e0340144a4164021403640c50500984010f010040815001c03400c0c030440e400703001e400c104000034003030044c0c0d024040000e620394242e0001c0003030345001d00740324004040440741200c0301124070005503d800b050803a0180940f0380e480c400c2e0041b0301b10392010140e5601840516015540244111b0056941400981440801520701040391009450310000d080b0450f0192828003e0244405030780643c0002d0002e045030713040c1d400284035154480001d10b80404500402925a100d41003040e1071094100e001d003c403074080d2001d0011000100040e0707014001c117142d05020f046c090001e9802c5611480f846c030881e0703980c94082d0710208020500e01341050710981121000d41c3d12030052050740a241104400205103440c000441070344a03500003400d2400600c0b5400200d030020000c1140b00076086840c109803044820100051207000f0202e5010741021603054901042103207049020744101c5c007032401d0030204140070b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 917281187 1250 917279937 917279939
    0x1a0303040902090307210b070f0f030f0b0604030c0f2c181b09011401020a15021303030c02030c0405010e13050c06041d0c12010611030d09060b040b060301050901 71
    0x81c030009400044286a040c03058076070000d0090348100c10114201e1b2011410400c5034524180a403000c14003500040c10005500c0b401c00704170b0390001080420f10281d02c0d011407070003d031b07108400c0508942402c1131361094001138000100302c5110110400c40b080d41c560304041607a290055058138004481da400d004962404055405c404940c0b419071040320801c0b20207070003a0b03088806203003a400c10444a41d030102d1010b2b07038070039241c03101c2c3c518014091000c80542411815000035154007241d030004043c0c100007030703162020352020f40640e4480d19200111405030f42c0c1d2410010408610050300f0b03070103800350b410345a03000e00705800b4060596030340300c94050803034039001c8525140f0505160262804e004002c0708000c2940c80300010001001d0b440700303a41810752446401088298068058641c0c050100800c01c0191240850241140c14a00f030980c0310400d0030081034194400da00d408030b01c0c41c0c601010401003168650103081c82c032005075800c000400c0c0260510131548802c0c042e0365401502040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 917282437 1250 917281187 917281199
    0x20907080709122604051903021309051507050301033e010e040f02030a0b0d050c010f1e09090c0f0503010509070e180103060b040605180c0f0a020c03011a030304 71
    0x354141643e205102c1400c141c0c00c103840008401d44c0810050b900c1c640005810070061605503084107071484e103d0b000d101450324550008000c1007000722001c144d030392218110004c4c80001e1143c1000394040005079040345c50040002001d40d4000d00045a5035140c011026040d81000a44a603104102c6681c07019405e00f01000148100140d940382410084010b4240000e502c541c00352900b071a03018600503849007070189200c0c050300c440e100360314010710002c0d441101107000001d00042c00002801c0544036100c040d4021582583c20310000203403546c05500c40f14210340e000041d6001c50707251202c10080d180c6c020404460b40c04480604d400083e200b0701c014000c40ca82280b140d60440041d050160100a0890205000342c40c1c4404900301c03042c1c030100410600c55103004504d43d8001c111020000c3e24101000038081410603240e0a1080385248001240486084101c0d981c44c0e4142d09076946030303c4a544002c0d81c5018080c51280a03500b011343e8400c0385426414074581c1524000c01030750a00b81010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 917283687 1250 917282437 917282459
    0x20d1b05090d111507020f010215040609020a150c030206010605040b0f030a090507230d02061204061401090b0a0b1206060f090d06020a1701030206041707050319020907080709 77
    0x50b8259046a10456007007402d944240c40740a04616855107a911010640100400105c848607168195000f0000b620410280c10750802c1d07026a010000003203287c42400481d20319800394000510f45040106140851030300110000911803082e82256000c1c0c3e04c680c8116284d020b03620414508074020301c0481c8066441034003031a40312940c60400500500c5580711103107442215401950303900300441e50344040f02c0500801c402004400d40346405011070940c04145a80302e0905417081c00194400450300704100307500486240000440f021a140d61901c40300c10044c040d07c41c1c1d09100748100f010000d03d801500c07050f5040c85621030310224965842c18140246588450403040513444200001c00f190703034481c001001540e001d8203005880302a102805071400b06d650306503064911f04400100f00580e42c0d42d040702c0698551480c1e00b941e41d40d220654a14100d11078200c030b039050103a80000900800207050324403603507008950f4a045915085d00903140c1c0700c015603141000880c6000203000c58a40d030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 917284937 1250 917283687 917283709
    0x603111e0103180b160207060302040510054603050f06010806010504090c080a05071b12030f290108010614090112051f080111071e0203070801020d1b0509 68
    0x2c03008848003000f59a100c1c03850b41801c60300350701c01e804842140189942c1c1040b20002521007400c0462404e410300d40015200b46a502207c810000300060700b000e45105124545010706282111010a1110100c00c4460042a07002c801900c4d86010f06800000c3c480d0090074010800d07203d441c101c0340c8a0500440b50700f0380040050741408010400020450614803d0380104116503448a0141c01d081c1c0151007941c1000d0100c00070000b1400038030000c031a01e5400004010740c00b001044c0034025101054014000b0350700d1182d0060f1a0004000c9075114417440080c00c1e0300b0603041e610008940390010349042d04203000c0c0200184c400c080306035a0a1030b820040914000504101000400320020401610f00441d041d80c07501901c400d00c9034000604280b04d0000e801110000d100141195200d40d0b00c40c0101d0230094034800000598068031413002c0101d10070560081c081d0b89160340c0340c40340c9034081d5100f5039280503000e103000d070303041e02c10903003407004440d15046a6221898645c075001004919855 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 917286187 1250 917284937 917284961
    0x11130c08061908060c0901031a130c120c05031e041a04081603110d0306060e091806011217041211010e0909070602010e06131209030203010f0603111e0103 68
    0x20303007200440d0030f800401c83d9a100b0090050007070382d181c2c0f44600040542e00c80000380940b00910b00308406250740c4010207244102d8410070001040d80e031302e01c002c6030711441c9010502c41183c0f601200002c1c00d42d11000551040c02d02400302d445081d480107a4036090031044502030650541018400c00302c80c1c000318001d8100f4010a100c070b0904240100d41031a202004d8001c030f011503803150506014003028040b481348420700381810401180b5152001c5d1980d40110059417088500c80005401e80010801001c1c4c0c1d10b000c0402c0300d8070741da102d681c00801c211001c5401c1d0361020300d0b0448200400740d00e0044905890340410012906051a594480c140d8884000107044c0018400c83c9005900c034134080318400d2501c1002002001d1a0401c044e00715005031889846607007150003040511044098540d0301e003940016401158480d05008440d25503064100950650070070f4001c80102806800803800d40b8040e82000d6141451b10080040913103282c454003105120b8100410b8940d80a1b07130000c5541d500d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 917287437 1250 917286187 917286229
    0x91503020d021602090f0f060d03053013030f1b0b0a05150a0302091b1207030911120601090203060f06030901020c070f2412020711130c0806 62
    0x404644010380e048190f807041d0098614070003800b589410b81907690000042840c41e100c07410f0414481041c084020b00c0c40340103000d030844810400d48643d0480d03140d1296004181d041203240c1480084c8000d203c140c2c1142d62a40c1b03404120b100d45c1030200c1d460b01984c180c0310031010380540e41007a00d03226220341c044035050820030f5001002c07070824001c092041d40d10000c0000d4a00d4407000b4400da107508904603a026091905042c00143c03501801c05030082e03800c4c100c0000c00f40f901c00d00b000182c0314250780340120038224802c0c44106a01a040301c400e982c400c01480c0788401c000c0e81400407410400c00d000156030311400040108840d585c0c0216080000905120400b110030b1000c606180d2081c0c54080003a03500145880070f5040502081014024101c501401a80740c401a09804c58029a03034001e1018001e981070815405115000c80f5006030f20301c02c0d074541c07616052003806040a49080c90003504c1d01011458420000e21895002441980710020203445000900035110704e10088418000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 917288687 1250 917287437 917287447
    0x91b0628030608010e0c03011d1f09081b100519090303181a01142d0d0b040219050a1205030c07031b05100e120c0a09021b03070309150302 61
    0x34800e006017101030785140010000740580c0c00c185800c403072410103814841c00000702c0c20f0112180101d94203039541500c00e490600100d2100d00d41001300804a070003031000a001072420540416a0700d241c500350261400d82c1c004000d04181ea0307040d00c03011901c030100708107281d00c400d200d50560750142001324040c1c5000030321102540c0c40c0d00300109500b24251903c0403554504e60880c510002c805014025001c40e0798141a481404260410f00d4070104404460500880700c512452518002c41c43c61401461154016020b0070280d19544050b0342c10380c050011400c120380d0a0182243d900100c0b03d0113011400340f00d1900303143c040014000c03401240e56000c1042045540394041001001850103118101551038004284446805055020381c0c010200511510326094002d982400000425201c030390381e4902c2d038031145040c110401079182d44840200707004203a002d440c0c2d000d01a400da0071514442c0d103810001400c0da407401000c00040004131448401c0c058080c00700c114134082c042c030b404d01600740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 917289937 1250 917288687 917288699
    0x60b3402100201060e0907030b0c0a0e0d060e01050603070e0c0d02120a020309070e01030302070e0a0e06190b030604021f050c1c140315101205091b06280306 69
    0x14070019580300107079100c0f0001d01131021407030001e9402c4140c0600070b1610501d556184450304500030700040305268086190300101e8000c5040c05400c24004103112180403140c070704400101442e040100707041d8a0100010700900340000c1c08010b82d198118414095582d001440c0d6640d400742d40c0c0780003001d0b024000450803c0480c0070003030040070b08440c0580c41c0d2130030320101c2c0c5c0341c150203a01010480e000c100040001c130b0340100300202a22030302d881c5400c450344c0703103c40b0700d01401c840b030310081440c0708000410840502d02c0b0300303a14805200c2c05090007400c0c506410180d840c502614041c0d03102d40c0a100c0e8084200313a41c1234400c0941c080307003040742c20208561000342c200203540300403200314440181882c650b598410500b11511844800480c15814040302c2d0031002c0400d03d0059005140c50104203190600800700c1217903051008000b8000c500d89101155141c07400504034006002c4254054012454403905644040c8001001140e072a107444d0742c400000401c0c144d40d4410f06907100404181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 917291187 1250 917289937 917289949
    0x3c0518010218030c220b040b030a15060b0f090d0309080d08160f05160203031306030e24041514041a070801140d0503210a060b3402 58
    0x11840c030314002181d056051400749130910001c40001803240c0140702c80014aa50312030000101213400038400507081c954140800c009009040145a02d40b0a01248000b000b803a034070b500c3d0036a2240f200030b00904c2d076910301203007081c0036440807850807075424407401055041144d8100c800e54002c0c5803017021b26642e8601c5600b09210801100c0001e69a80704001307031303180c0d0907201404c01e9190349803000031400c5180c80200a40519109840f00c9901e1540400565808000703503007042001015000c1569550745001c0e00408480d40d484401d0b0088540c07446d81c408811034645586940402400d0240c0e03180c1c1e80d9507403488030042c1625040d03551440a1816468804646031040f48a404d5078a8494619140829030a1005100d602040100c80c014000c210705800d458a03a0081035070655000c03202032800c68194064000d00321440d9242d0450304410040010455000300b020300c008004050300c40041004610880d00750011500c040303201800c2482c3c00c28405901403207081e81e02031541040d0f60000729 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 917292437 1250 917291187 917291197
    0xb07080f0c0a060506100801140307090e031806030108061305070b0a0f0201050a0c091211030f011508010507090311010318060c02010e0606030d210f3c05180102 71
    0x101580c8201e20382c00c01c0000301d108103500014100e801079000b050300310006000c0841401400d04161044040089a8408000050262030301030400d12203880700d00001c0e42e598100b0b040144202e14405514030003801c1a07000c49042e80c40c8040a04002c0d0b03510559164445010f40003120b00340704031003001506505e03990107000784007096a50b4150000d002c1c04001c0c01e4501c09410038100310b10702022061810780010b80c1000312864900300920580190520444041c4030303141b035507050300452254240c0c061065000000c2703034044002078034003241c807020000e0803038000320383c0c20000c00d1800301c0a202081104a00c0c180c2c1d000145404606070b80d00440406c0d007520341d420210342e11515203c0070b0449540a02403030f610100720100500c0b131407920100003a5581c06410785032090280140401c51440a082648a0104000641030155075030007224200101814411180e2004c0c0c417000c04986c0e030103508000440340c10340e551100c2010040c0100131004001c068000000186418903182120b4820b0005c0e02c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 917293687 1250 917292437 917292457
    0x8010315020a23093618070e010f0807060c03210f14090f10020a030b030f281203111b03070c050103020c0a0b060d0807050c0103110406090b07080f 65
    0x340d200d0300c101e000e0124103080002c040c174141d00b04084c0000140300c0d01c1421400b0140d55080e1075241e4481c14210310390848041c405c0e0141e40038a21000c1860040506058100ca030218038840441e541c1d25820341d01d4140e5030090340300144a105040020903c1031380c0203000000521910540001c140109508481481b11106001031712180030b201c03822801c0404c0c40d80300700e03520003030043d4180710041142c40701200110808850382c086401d80202d44a64411310140c100a801c8071600c0385078046441d510310f18a08007130900008804240200c02100c91041200c6502410b00d501b425844101500645100340d460302171241c00740a0b0849180410100d81e2024605801131a52043c40b800e2100051200c0d82005041c1801007080040c801d0001418040040d0130040010850300c817040040e074110b40ca203501030700075800402d560003070003400b041e4a0741d846000d032020040100018681041c0d805a44100804a441d040003000030081c030000408071075109000c81c61070301a000c140034245d070300403c03028 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 917294937 1250 917293687 917293757
    0x2030106090c180605040518040609020d0317060f0d03050304060f060902040906080714090c160b07031d1236190302030a03140c0d02010b030c0108010315020a 70
    0xa0b80f0118074000c448054841c91034090b18280c24540803e40f07098113048021024010180040d0510001d58013880f08540c1c02019401d5170039031401c0041035105c1d10003103d0040c041d00408a0b0702884e280e811b14006083c082c2021f030a0f06403944003500d08d600001c0059403141c3e261102106501d40c140701d20000341440c0100141c4960500c00f14100f01c640a0300000c000c1c0c0c0c0914000c0c13041d450300d000920900141141c80900a50790700b20b52416034010700400d0380b040f5021407003c02c100420154628482e1440e80d03400c01a03655089000c00d10121100f555020640003805012051961034000300a904900e0700c001d442e054030060000f10302c8010891406825030b2001c024403081c0f52117507140400b0036200251000090071038001989442da4150014244801c00b1407080442c8040300a542d14610040c0a40d07007100ca003828040d020b040210b094520078000c0c400c0c116020f6014a80d80c1d8180c0e900240c0c850940c14141c100b00d002940a0901070b824003003c2c0d0440c101c10500f2907854102412140c40f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 917296187 1250 917294937 917294957
    0x7020c0a080717010e0a1b033003023f0406060303030b03070b22270e030a120b0d020303030103060605011b021e0a0506041d0901020c1902030106090c 66
    0x460031240c40b0039850350301607414030100e4001c4040008144186c142c202510320464041c0e110140d0410043da48010148010900d20000a84014030310342003c05110623925071224440404900f24469428140c04c664a1701141c140c1006c442c3d1034224000400210340000e4a01c03592560600120445d0104c5a56888030b50a10800d03a1500400300c000005600401c90f00341030100310303030352400390100040e08085c0f45e17100202c0b070f50f55036103082004021540d0411040b03001e04401e0100301c01c00c0082031240f0b03400c000d020032035050000200c4001030701a507a0121042c0b516400b034406420b0f80c21409a200b001c102622001d03941c144025402903120f08800504c080ca0000003508041c000b0202d85221413032005060b000d6280c0c50201c001c0c0c982e110340514408031316080090070209141d04040e40005e4049800308211401c082c903100c2e200b03001010340082e543d9940d100b80c241e1258801e200c0641c0c00400039400c1c0d81b01100008010703d0303c001d00120b00c007034036807581074111403000030030000107030320500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 917297437 1250 917296187 917296199
    0x110403050616020604051c05040b210f01060c080f0c060903040e16080c030601090b0d1e05090304030807060e030d090201230a1101060e01060e090f1504020307020c0a0807 75
    0x40e020386032510380050304c150f2030592642030310340100c030100d052848801c03242c1508842c49941140d003c2c01d00c10740c41035124445c1d06048003070040e18005002d410002000401d201c100014003d074100c44840c6e580036190384040d0303203444c07036508420301c10780140c07800f4000c1c40d242e10014061544034080d68002151242c0c50a410418134440140062184000300328540c00c529500c220100d5125101065943d52500c41200499482c030a550014101e100041aa035841c06040d81025000c040e000300f4a150683c104600c2004440081d20b52155076401000100f0009501e04040c00003607004c1e13040090102003181c50641594000741d055200c407940c5580030811580c210700390b500100380c9522a18540700c41030080c001e903841088440014000c071900206404882500044082d28103003c101101e540c0d9030002518000c1e40d4900c0c0c80c0f14040200008a211840c034400c10310030f010101d82c1c005100021000d0000030750000e080d01045001d00a00700c442920742d0150f02c80103041d104000d0541600e442 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 917298687 1250 917297437 917297461
    0x302030f0106110c0402180a06020f07230f01020a080f0301030c0e0f070818070b090f010c080301090b180708192904090c17010c030608060403121104030506 69
    0x1810020902400c003070143c101401c0041d40782100e81054a0040c0e48030f0485400c00800341c55040f04980c4107902c100302003403803603007c03400b940e946e50380d00c04840c0001c1d1070768032303020200c41e2100409600d075014605903511403a058035001c80c114010f00580c0c008541c69104d00007030b603001219590304020000010010051000d500ca4001e03c21746004440e94200401221544400a0440c01c1044000c401050001c036500c0d21a9020810303480440300220b684d41c1035032107540c01070743c0e0b03003441a500c03002da503101ca501444114810a601810369451a802c1540203001000d40090740d0313805c0101c00e0020310203032800070304440c01407034176072140010340c60a040c5103030b00310755600786201135541009000d001e48540c0c049280c1c0c0c1c070080c9541141480da1140e010800826021001400d0030840c0030380000c584880d0810242080003500c02031003c030302d41c660140c054075000c0c810b52040750b10031800a0042403140c000c00b10103290440b4045544e00342d00d025681d240d045074000f030301c440c5c02240610140c50001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 917299937 1250 917298687 917298689
    0x41b032901030206031b0d02071505010b03010b030c0d060f0e0a0f180b0406090233030c040e04030c020a0f2606180309031c030e1b04020706020c0601060302030f01 72
    0x280040d801598150ba000c42d0480c000607052401c0c2c0c02c5901c107404d404461072029038065508228003107480c1d8400c2e0802c95038400c3c080c5800070080d4608400031454005810882741a1032a840c4503500c1d507160500c10180e07691001f50005038065440c18046600d43d000c1c511403000f4a58802091050300740780c881ca404a42c8502e0011409038a081c4445c03407000286003106440030380141c10f10441c0ea40314140b0300042c11148000940c0208041c01e48420349d501c4c60750608404c0310f0340c07000402050a80008004a1000b518020fa21490a000800c1000000e154280e8458440e1811036043c0c100c542c00310b000308242d03800490450614550500a03a1381e40d0904000b110f0040710881c46060118a0701d035110302e00074002c2040706a88a04a0800b5001003003159040760018044600000c0c0f5441440d041c04e8036118004002420901900220200003940015801100c4040c121750784010341000300030b621901044442e40e07020b10440072100000e201d19130013011703151809a505d1602804040c088001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 917301187 1250 917299937 917300003
    0x23120301090e1c09140d15020c0712080d0911030106031103010b0103330308031509070513061803060203010e040c0b03070c23010218040f0b0102060609041b03 70
    0x3040e00e40f20801c5612190718030848034505510340310b60f0101d10109280d40b24501014040c0740c1010782c6142a401c00358000c1041015140660700741644410490b0f030050340030b11014100800500c580000005a5403040d9911403045907174072072095960303001c2825125998010307650b40c001084407a1070380c10300b030003500d404200c00d20302044181a54403000990040056411520014a402c0e8003000c4043d00c0c1004040c58010f05450746a1906a02035010318100150b1280522007400c042100781b0f01580503035042e54108241307100e06605051007110540c1c61030303028000800c10382e100000803d03d607100660282000004041d52131400d4103240d02c04c03038190b600c000e54003401003080040b407540c0115400c28640d4070661100380d401d107424a8514294216184805552001070b050340c1005c8184030400341203609903810311200001c0074683c0c0489100d60100c6005da003240001802c0ca00c1c000d10020b5005104240c0c660303448440485003041d9000b5500202d9004846e4004000c0070216105004032030381c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 917302437 1250 917301187 917301223
    0xf0501020a0b0f090a0f1104110c030702090a0b060a030b0306010f15030c0e12010207030815012115060f0809030315010528031d06010323120301090e 66
    0x18a03a640c00403507100041412140300403000100d030040d00c05214641d511a000f408517801c031b0000b070030481000030703401c00d0700342c4510300d0242c408108a07084403c1c0d40501c1008005581042c0c429003c3c011a10001814500b909a50b0a030451084c0e50300c0d0040e280e5881c00340d0303000598030502c105041c901001030301b02404003c003000d4204001d006600509445210501c1c0204141d00064410703030340720f80e4040b20340d0350182c04201d001c44000710543c094200c8034080e59592006469120074081e03c41600d4503524000390b55135400c1b4900302c071840d00380010202404030004100b05103aa05101340303401900800d000940d142c03d107924882e448100c4036040710312100551f00e141001030003507a1145541c55164148100030030b08100100712040307100c0c0c00d81c9500060034038036440314030024010180c0e00c00500308801900e03812154044000382c064143c07076100c0d4041c040f0581c802000c007508441907003603880600c501580480e02100703101c00782d4028070000c000030542003600300b212420030042c0040c40440304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 917303687 1250 917302437 917302453
    0x9011508030910210c0806030d0c0b060f010e04090f171201120503130f0f06020a050606040e190303320610112b0503190b1f0201060f050102 62
    0x160380c0081c800c02c3c0302024108800c0c809404290324540442e8101c011408070702e046000d111580e04400120f1141e0011815120740c4032a14100740c0340e4100c201c00140141503050001201d90030f04141825142c0014184228203a0f82880000c0580c0c11044003102d01c40c840c4000c2d201004001880340f40040407903c03216050400c4e000c030140070070105106000c0c1d5161012400400e0201c18001c8440482c00c1c20748403000c85440360044490b02c83c5600c21109800c2e400e00b0005440d0340702141d03540ba8154080041c04468448400708009450380070455941800f070301c600002c040d443c0ca071052650b14440c0d00c000c0b80d24110b4040241c000c114011a650407030150100381e00201c0700003203090b44e110b4000c40c2d8001d80186901002c4400381c1403c4207908803813161150000c41441e011122000d42980800030120410002004903001d00054900d4540e000e00103080c9483c4254641201d80081c1001d0801c140403c890034420147c40c607042a1840540d544d80e00038496408095842d4001c1d110a0000b00040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 917304937 1250 917303687 917303689
    0x1a061203270d0501050103020a0f0f09020c070b03041b05040b01050d0c09170f0607030c140c0a2901060f0c0b040f0506010e1501020109030504030618020603090115080309 75
    0x2445108480c845400803000300211504080c200050111400340c182d03108640750f4541680209400c1c0400c1e0b114203071220b00051950320f5920b42206071803160300b2814040d072900c1c111001079004034414124501605c000801c0b611803001c090741c030442c02425028078114100c8402c120070f84164000703d0095040060080c042d0b40c03c5800c407000c2c3c1201502c0020f1900d1600070071610fa003e103800580c0204400315100d4415000011015400019442a100716031039900040d012600410840030204400002d090707880501400030300401c0910100707650103040300b41d503100004036092800500800610101201d60040c0e000582d0262055003031000c0507030250349015107407400c0c0c5000140b00440a0b00000c00704150198001061a40641252070030750315645030b0310100c10708a03020a1105164451440c240d8414050582d5080c2c154036941e10301070450300c40030302030100c07201142600302881c2c101c0001601c0e290700462140400e180005486120001d203d07c0b03c08965100c0c1c0e495500030b00c008402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 917306187 1250 917304937 917304943
    0x5030f0d052a18060a020f0c06090a060c052107110f0120070905012402070f050111011803031a150f030714070f060b0111060406020c16031a0612 64
    0x16041c900e250345440f00d101d284410030b9041c1003089a50000070100d0380801003600010842c42e0300d00c815099440180701b1206002d00c1e0300800b0360b0039500c0b090803282000043e0160010108039402036043d10b1908072443c000c0b40e8614207034181010804000585030701408502000740f1104402200c074004010020030000303001d03400d095101100e14058100c40411001d00304400310040501039003d00c0103683d60f540d0019010000f21502c000302c000c80103101100783c4080f6005050f00e03084600c3c601c45600f02001101c4600002c0907540044d943d0b400c81002d2004003415452040741b00f9500480c240d80403800410b14103100d424203d000301001e48500007002014801d80f0551501002540d44030358544001319040c0e2440c0c1d03044c0c15809400203c00701030010300c600000c50540100c80c1030055004100045400c055000c21a20160f007085001c40d00241080d0000d0080c00b51881c1141c02d003105040700c86107031220321341c0b04540d41c0031084030300d00005010f0110701c0c0e8404021240c40007000b0780c0c0441aa1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 917307437 1250 917306187 917306251
    0x2010e030d1706010905031507031103040b0a050c040503060f09010e42010e1e040b04020d11060d0204212a0e09010c09320d05030f0d05 60
    0x1010040e80016041d64422031703088004290040445540b010640700d10b910480007503507d10300003810000c9056041c00703903c0032a8012356108004400994500390101e0003044050804462b68008000002d4a81d80c1008128000c0202201c18020340c14072032a46402c49040a440028a4110148111009050000c020f0015040500484007a0383e20b40c1c400b180c0702c02c540c21102d03440342010008522407410b140018400c80806084c071042c6a800001180c09180880303004051454000c00600181013130120784048612490400e160300c03d01c00f00142c81e6800ca80580445079a012404004100800010f1004a000c8034208003291520f5128142800d04c103c14455807404072541d001071441503106407070004c04454009040c02c2c00c00c602624042c2c208207130b0b000b000072118900422000c1c01000b11260001840c403260802e0700e81100740c6641005581d040341e5210003821901000310f041030001780361141c05403140a6448042c03034121400c950300036208a4028443d420000c40400c00c40400035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 917308687 1250 917307437 917307467
    0xb010305161b141c080609070c0606030b0705070b0a0606020a23120a08150a050d0201030908070f0507060e090a020309031611031e03040521010c0c02010e030d 70
    0x18001c0c1c8401214000d002e40142c0200144038100c6002455900815a00b402c011070030320100041c14580c81c02c071001441a01c2c0d40e64450300c903a001c900124060002c0c0d0602d0751207a40d01180c00381c0d80c1c4c2c0314400b085e4000c443d85000b04400040c0d503000c11021420842d030103d604841009100e0811000075611a0320110062000ca8441c00401604541460410503105408201c5180310000e4a168805810007401a008100c0e0341000c0358007850401c0d40742c040e420000e031548401e1450704003009111b25034600e045c0e040c50b940e080c0b181c0120b4103000c01800c3d07440c000e1200030101425454040d1402c07540d43e009104100c2201c4482111350b9a2100703540c0c00840d1406e0150300c1e510780034091401d510880c5c1c4c05001c4d004007940703000c04200e0b085c00c0e484513a0314100e007a1081100d61007070790007600e9904028007925800420051040d8607044e0088103400000702c43e40c010342040e4004445c00c58201d5243c040c00b00f03a110142e9404c669200307255403e4044154040c0a40c0d038030048024040c548007208103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 917309937 1250 917308687 917308697
    0x1006090b040608060c090316140901060f020604080904020909130b0906160e04060803031e06040c091a090a030606050915090f040201300608120403080307141b010b01030516 76
    0x1410b0715a0f0030000d0f84d00c0142d6001440d40c0c01580c4141614009007224009c034040d1823464000654140038445007c00300355541c018160907551961241000c0e88010381c202d0b0311503400d02c00c444c81da8483c01e0680e032003101101d000203400d41540c1880c2c4000400204180f02c90303440f00c1c0c1000303c04203111580385400b03034080c18010a0140300384009800381c0829004108244070100410400054070348800740e600c0c81144d15000035458240c10700c01910800b1100c0be02017110182c04100075a840c4240314a40718105c81810b0400301400c1c000f50f442501076006039a0340d070b100c2c1c01c02d01061030100c01d03403600036192404a84001c07041f08085100d1050003030154100c801084c001409690240c505501c08a107100000243c44401c1da4131882c84401003891008454500302d0082000203001500d82142486d0400035410145190380c1c104103940b0003091b86080003628084d90340040712032409080c2190b100c12100350b40040e0f2440040c21a0010442c1c50704050030036050002000ca00d20b0a1010702c8014502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 917311187 1250 917309937 917309947
    0x1b050f0705011d0327030c091801111902010204030b06100c050303131109130813030c14040c03090b07030b040908040807030b18031207020a051006090b040608060c 72
    0x301e0040c044040c5005903c0c801c040f0190000401000034103075008000d4004402d141e164401000c030f02003a070700702034050340002c419403080e01e4207940f203960110300b0760030b05100070044240c1e080c25075149842070360a0100209a5404164904144844819080c4003c500b0309186840320080000d005e8185c80c09100d0600d4407070845072207400310519035074001c411640e60781131039040c8081a81071254191001da5181c600502c052424031001030150901000b610b8041c402d980b074880c01580461100a01d1034481a400000074110004100c0280303e034469810b0f0026445003480300b960b3350f2035001c00400d441c0c03000c0030b800240c0c3c40f1025500280545000107102d441a00850014651038602800000020030000f44054000581c00f095038424034601b8170a44130480401c40690b44180380000f1600184050f1500c03580c6c0141140e0f005645104403814801c0548585007003000c22a18602003e85900041c00540030a008604c20143e0584003008150728080c41240c4030040582000a11000094 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 917312437 1250 917311187 917311193
    0x21003020d111b01021e09240d0f150b0c15040f030905030a050307061e02030a050f060a0605090f061306050315040203090a111f121b050f07 62
    0x41910394070140140204144034040d0000d504540111250a11031401034200790440e00040c02030722080c0810301008030250010b10013400c10343e00f20b00da1580d000a4031030001c42020a150410740d40b0038014403003107a1f854250b04082c10503034090404071500076080c4903041020f40ea46200060403110741d5450307507032a210200031640c2018010440c0320b084a2640f8140701c148040e40f0000d4000500c02d4544040c013550b50814103445501c5100301400d503400612141003c1001d075044071900c18441c0b03041d000c000100c040c03d201240c00c1580e1007681203a6031001c200021410040c115006201103500075045481d00d84001c0507441560321080c040c070807580003403045803600c000703036540a450806680082510703244003c1c02600301311100e4151034400030100c003480c14203100700e0340281c21143c0902900e81040e1100960210840461500f00c0e641d0406c606850041100194455425030390301c2c03071a84c101048203c01e0b1110b100f81503102c010300c00c07003507509160060202c07440840800c2c0b015840c2d21041c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 917313687 1250 917312437 917312441
    0x304020d060b04020f120a0917090301020909041128031106041203080a180c060305041401020a230301140d050c09070c0326011701091a0912090d021003 67
    0xc001c0343c21500100c0c5004001ca1000c0241c80d201c0d03c166030149195444511034429240c1340c0c43d01030010603c0c80400c000a51009008241c083c001038005841c20081201007401d505080710f094410841c2c90441c40020301e0590343c0780020300d1008940e0303941071102ca070000542c1c502c5072200074009030525080c86413940b60079064400030854880e000f04030034414100500f26a10460f0000c000524020308252412407184180200982080c84001c47e04c4c00c044003038009142c05002074804150680b0030b81004482400241f800e00c00507960b01c04032a01c0803100e1a900100040c05000400040c0018452035400c0b01c444816070508a541d0382402c813060802c141000090000c0c2c0e600000d00100700100780350032950b94495103200c0c1c0e0b10706100041911000030120348410a68483c83d00b903100401c4200340181c054003014400e00000500ca5029a807045143e0030b610760305c0d142c00300d401d00800400398410f111140b440e0703113205030b41c52a20703070f601c0002030000c061810000e20405a01c4c5040f2841440b035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 917314937 1250 917313687 917313701
    0xb0409020a03120906020313120201020c0904080901020705010c080313080d09211107180209030316140a050604080a0314090c0f03030f090d06020712181a0304020d06 73
    0x5800d8460041e200c3c1094030750050141d1209001c540c10001c0001e500d0310010486001004001064042c41d052400c030b4500c201c1c03000011780c11445801da18407010781c0e40c0303002c081c081c40c401d0440031f990300c0010001a042c152030b540424144001c8411200100d19001c046a80c411000402d034044e1501e00d2030302e800d9034000e903a1005425072030041c000c820411a00c918090359241031400000124a00b001240c0d61000388030320f00e0a94100390030400849c40c4c4801302d8001c21001a0001d810001c0160100c0e00d1030b084400040c8420041a030503d0034003010004812004032642c019010540c101d0b100c00e6510714014100900300800010071007005c503c00c1d48200c258810400c11600740b810150748284da04ca190300000b52207880d012200c0c110f60301e4000125060182045509410681e9000400040581880d402d036440b41d0200094400109005003032000c086480e1521268140c24844018151501c0d40004d0140804607110000804201007669401a81250410b0300c0c8041490304030050081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 917316187 1250 917314937 917314939
    0xc0f0801030f050109050d0302040e101805060303040801020a0903020405060a1d0c1603031e0203091b03030f0408070f120c09020d0608060127050105010f18080a11131e0b040902 78
    0x7c0c01c0260840c00c3c0c1c5a0000d20413102200004100c0b5160b41c0c1c80c10300b86140030300c140d065001e40c2d41c0e030b41c1d044c004464010a0b80054020250303800e03c0d64909005003640d005105003030028024a0080c003c5252500c45c05411a4013030b2102e03083d03d4100305119506541e452201d620f094200700014030b0510b000c400f101e2110015061048110540e8031b005405003040f4003c0c80c0503a044506a464510b00340e00c2928802d440351002040c01103804100f05000060030201c00c1d40600041050349007040d0600000e000a040c840c4c0104413044c40d005150019000e560000c060702d014150100e000b10386c0030b00c000d0302642c2c07049000513a070b4950400804010120740d803004000d8001d40d8000190580221001c8907140900401c1c180c402c80e00a031441d0895000b40281400b258003602c1c40c15038140b154000310341148aa43e4a4107031140c654450714505908050f0440d040c0c21005e198211904003901d07040d944c0c10340350b40c1c1407048804200038030645403845e860411b1540d5031810070300410741d03954000d042c079950 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 917317437 1250 917316187 917316193
    0x6130b04090207060b0108101a0403140601170f03040b03130605010303020d031a100804050a080c0d09080309010905010509130908030702010b0a120b0a0624030c0f0801030f05010905 80
    0x25481c8504000794210b08001d603644c0d881d0413501c0602c5c2d4003901c040b611803511048038010590528250420709030315a00f0144880c40140004000039181c1c040c03d9102002940080c405503240c41c2c0000000744100050640a8020b840a41070040000059405a442c00391142d510717503488101441c501200510060182c40c00c100001083c5174020990141040a682e01800b29080c400241408403508a01240e00500003075184540ba0b846540c907039030410700c55400e4900b0300703446d911070a07980d40107110042016000131108008aa0304100014001d00f0a03401660030584600c5c0041c2008846200f030b64180301000500d51100d03540c07484c1020503001440020400780401e401c1c2521250401c6400b81c0240d8603000400d84103140415035207013181c00d01c0b19041407441c032075610347d840c2e848050039540310345440781008212001c1550015a800003030082c181c100e005410700c010150b90011000700148000031081c4a2925030007152941500d810030b844e607845001c2c80c5815070050081c404050f00d940 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 917318687 1250 917317437 917317439
    0x3080f030a1b09080c060c071404110a27151d0406091d010e0a0813120b04020103060603062d030816051605060702100917010c080c0309070506130b04 66
    0x3d400c44080c1081d10038140858201608000a10034107200d031341b46d03441c000d44c00010104050070650601d20260714024101148031340d8090139256030794100c0601900802c0f00340002083c800c86143c152201c030414915441003442c07400300350144c90302104035008100480d584124a246540c00500f0202990203081001125510440d4800400d1411448030101001c003201c215120014054101440c0f840d501500901c0a1076482e4074007a800b01d55038851542520000091030308410100342c1d0028001e00105804e0b260601c00101180c3c0160000001d040c9080c5c0148500c0c3e584001e0a01c407850810f0b0010010540c8103994800d000c0c103903100500c0b801c00007568030503903c40030320700101c450700c80c50894140081484d034070700d00c0101d540103003904298140241d801515051601007007070324079030070401c00702525114010818031030080e00301c019a44030180408925131050030381358055030410b905030550034a07400c51a1a20218030900c2d2090402048149524a205414500038101300019691321 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 917319937 1250 917318687 917318741
    0x110f070915050a0f2601060303090519150e041e02090a0b0f030f04020d05010c0e01110f0303012702030103050114060f0a0b2a01020c0c0a03080f030a 66
    0x60005540401d200d6035440000140301e0400c00c00e540143d542040982a41c070b030030809284080212039a4228218841000b441d209900a200c0c03400614041c0d51807404490601c0d00b484212001c05d000300c3c0140056410801c1008107501800c400a881480c0503202107900c40e00080107056546d0f00c40100400302406001000302603030061210120a44841340c1e21562200000001d01401140d400c1240341000000c5000710150340065100744020306d1004070119640380e19017180c0301039803224089070001950075129a001082424850301d0301e030040c80000c0031505420b0312800103120340e082c00100403442506a000e084245809407100260031034817903070f403030a102d40030300034410183d001240004046a150700740400700c1600d5580240030380040500d040702501c0b440d0701805c841110786920100608154510140114509180900242c0c41b030500503000d50802c1103a09489109080a64041001031000b500f500d0746410b65141907070f243c3d41d4041203038000c1c0c500f0205600d03111041901c08510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 917321187 1250 917319937 917319941
    0x1020f03100311100207050f061c1a031b120106030b0408031e01080a35120105100f030c021e0607030c021216170f1908060a0303110f0709 61
    0x112801040304460b8901603c05101148801c001e80c000107030003910f401c3c080360030010b203030300c0b003c2c4000f40040380340907070040081e400700f061003003482c80300341e16203c2c00303012a488201d01c81107241045001e0304d100d040e00c000392110707000541c842d18001c865802c1c00304110340b001c0d400750b0b00443c0c01c0703e41d1402c1850103203000c103c41d92040b580e940c180c01032200c408200800c840719090581d5440c100800c403484042d154641c001c0314034000823003070f00a00b40e1035240740d51440060242088a110802d80c85003484c8585907203d0805030002c900542203008125602c41d44520642d082100038200007545807000c04003241070103c582116000d11403190144101c000002449030b1180d03900c1c6c0d40402ca02d00700b0b00c40c100d0300c031008082c40b030407401c0f07060221281d000c500540725242c00b071240b41c42c3c0c02002c5041c0490807098200340d14142501c0800304004405a15042d0040c42005403840c2612681c40c0c00b00004a500c1007138000901042221894400011000c1108038109541c9c00f003220a81503035100c613900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 917322437 1250 917321187 917321189
    0x1f05060a03051903121b0c051015091406151305150309060a1427010609090c06020109020105031902071b0617040b0106051c090b040b01210204020306010201020f0310 73
    0x80050400b29102c2c2c800201c0344a0703104030340e800e498540000100346c3d8081b50b40100c400c0c010340350340c0100400d40c4800d18091040e1480e203034804000c0c2210502d8008a07108649800030a0060681210304100d199501d1525801d8400c020054594031403454512104803407003e0340050380c0011080a00911958a5002075071080d680d0741d044801d1030342c482c00310030300755000701c2c9003401204118004214443c8200d51840f1400981c161005501c629050186081d65410341c0141d8280307036103020510601c03810b22003800207042c2034002405040c3c0b0790750000344180700081c400325000c81c10343c0341412044000d07011170700c20a40040c800181140c00c0b0720742c02c101d070383c8030300c43c0d42c01003008980900d0221400042c01d5100b103030080c3d00000542c0c60134905031042c0d445001d82c1140d0050116903d06001158851001c21902900c5884418517282c545200c0075403041e0058070000300850000340781d031603101d5400b0100075415180561680c8035000143e0180c01401400080280701004000d145242403002d20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 917323687 1250 917322437 917322443
    0x3111504110d02010e06090f1c020a060810061412100504062123150106120218010e030c130b030114100317040906030303020a0f021f05060a030519 65
    0x109035540c07140c00b00310481c0c1c900760000303000c42e1100104030094a444405041d50f003001031f001006842180e4001101c401d648420f8200700d444460b450819070a00b612104094a82170411941078209605001c1da2881c21f4800e060400040b0780d00c1e130004000200030340b6680703110a0a40049414100c408010303041060145501076460070000241d10781d07000742003500b07003d400c1000b40030401540e1991030310401e481c641c402d4074200c6a00080700e1040c0c101301c104102e10380245190f1407075041160081c0b98407800701d40007000500600000308c18021841d000b41c0850400d082840e90103440b5000709080c40400c8131200c1d8880400c40080d19100b40daa041201c855804400030040c521920007c0b00120005035581811810131000500000e140c902d0007030202084a61828100759550b40e04005444440e0400c4001980100f859448203030000d1030117151f10322500282140d40c80307120901c5101002c5049401c0c0342621600880d56645450895001a43d084016203040d0b51450b078002c019428010011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 917324937 1250 917323687 917323703
    0x20d060f2d230c13170f010b0319030c08040506030408070309080d0f110c030102161e231903050901030b010206090318060717040f090527031c0b01020c18010b0703111504 75
    0x1150343c03460301140d2020700142b00c0451152030207282d102100c1c00750000a00311490281080080b41030341d580009103100314031409419594445034a0004c00b598055403040c110340d0302c62140c1d00c4810f500500c85038070701c6c401841d02244100e00020181d1600265100144c2c044d440010000e150002c9000a00c000070300030002c840041e18000040c1c0c070321141070302014100240011041a050b140300075203181c1d070304103601200c00400c0d008441e5404003550820840101d04000340c81d039515600341c0281090340b1001d0000d0030152601e5003046460340300e155078640405459030382040840c0e80340c200740c07080c150b084003800e580601070600d544c0389580180200854034094000000d4a2202401070038800c1d444140d803440384420000e041d4400080381da210800e580403d102c002000b2002546e880301e4454220f601003242c4048600190400c00307036802040c00740704904904182e20340c09040c5141100d21075503203103a40300300c503080446030455049448841360160200c650484144204828040d50080002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 917326187 1250 917324937 917324951
    0x60c0207091d0606011803050601120c050f100503060d08130e061507030302070213020c010507140703020613020307030218160c020d060f2d230c13170f01 68
    0x1903141c6109581c060700102d80d102c0000240107501c102510642c94001d00c481c1c10038036450b9a111410500c1c2600000380d14909804001d050100c2c80202ea4020301c1c055a442c401407003000b01040c100354a1009403130a01c50000007064150301c03000c1e003800e50b641d04460025181e008038210354400145912403941c074070880502103411031402090040550301101011031908000e90340030740280d0010102a42e1000036040d40d00d0a402d0540020b0240700886000050039141c06040a81398080001c13440e0001c1a0a12801c000260002070352a0400f0700b000d4400481c0c00c0f1840040c0c507000041d08004c0d00550521072140c031a50076061017078001c42441e4030040c60403201306821140c18031000c5001e5408003d8401510100c5c44941c00004241400c040200b845900c410650110024400e40d42c407890098081c040c0005449104d004240c01d146001001649848103104141090240c006160040c000a0106420f403111407094020013201c0490101d580c1000000c2e500c501c4c810701c0c1c1014950030008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 917327437 1250 917326187 917326211
    0x3181f2f0f0f0607020f0303040f030e04050c0909010f05060414120a080403050f0a0b0f090a0c15030b0d020d02100315060825020303010b0f0d0e1f021c0902030307060c020709 77
    0x140500b10010800700031425270340c07152212414985544015410300205085040303868a46000e40d6215440000b013140e542c4010700c06002055030142d011001c04007406400b0b010131344d603000c1140c0484010030b0100220305e40c0400003e44030325200d0250b640d1407041c07521100c10001400043c00c01c40703026005032622072000c41c4000340c03100c1080c10018100a03c000005958070168440d031900030340702900712502140c8545e84c681c00e4000c147c00140311920400500c401c05981030041c41d868000c15104111007010940c04116101d0041100920621320200c12040d0300b4460740c81a8030420320088400c072884d941c1c032030142c40b0141c11b44050245c008810404601030380c00c2c2c6980b140e91600d540c02189180c0c41d1040401103a00030400100003100d040068074192807003405030045035204400641202c58413602e850200150740308580f8411401404001004c2c0e445108400340c51008010100c1c080105100207402c621440c0c0d00200954501440758240ca94001040000da1300000700412415100356 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 917328687 1250 917327437 917327443
    0x506070c030210020f100e241f1a0a050d05040807030f0507200a0518070306050d0b06010c02040603061404030f020a020a141203181f2f0f0f060702 65
    0x149904500743d0000309451020100d984c40440e04802c0b11094030008d01c6d002d240321403200003404113080000340304000d01c805144a20012140b5100708500c00034000d1034282045000c80c142c2e1000c0122040120309040320a01410403211540001c4104000d0341c03a191401c1c22484c1c00000d070036000560800030307075100300780110b0803100780580208000c031150101d4854000c041c50f0300000c00e47c100c4001d500010b400c0c0c80724103442803101d10000550b4003518100030018111101a03200d10700c5080f50504074004280c1e503d1465800c02020f2a00d0310384c08185c2d0010401408207644001e040074a0305c02c0040c00340300c1703143e1407600a43c42544c03506002e02640c007007269100070f040c0d4081e60286880d6000c02c101120a20a01c6c1030300c1024000404102501881c01e085410040305031440e1006000c1c0301916103804e40c2952222405240714402d10b610150000745910b070f40341074400440c20b1006000620b804110049400548590200d079401c00303000c1c2869880e09000503070221644a40004181e0b514008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 917329937 1250 917328687 917328703
    0xc0305060c041d0a0209040e030301090c0c12050d02131502100e0c01050c0f030a18060804030905060c0a020a081014040b0f070c120c051b09060d08040506070c03021002 74
    0x95102480702c28074443c0d00c0d02c0303018040c0c0302122050782008a44400e88840c0aa00c0910032981d006e0b50b107a43c901002d0005461200c610700040005030a203140008041042c0212502d5040ca0200e4a40c044110300b42c000340308061004034440c1d00ca0000180c10006150000310160081d429152000030b44043d60301030b509251441010380e040f103d074012181d48140040c10b5625419001c035400600340c01c880303a0855000f544100001503114110b074690641c0010188014460781c50071810520b41078a004001418034010703103125079000140410b0f0028100b1603507880c560001c041e001415039a55100d6524071180008441c0d03107003000ca81d65803401003464014821600013414861a690301d5082c600549801020344007482140174004022912039240980410f901d6190380d507a030702c442d0514907c1e000e004020059086503030700360340c000340d240d40001580105003070f2009112002c0b140380000050086401481c0c00400c0490f0240c148001c40301750004880c001c0c0c030014920038041004980b15288 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 917331187 1250 917329937 917329949
    0x61b08090712080405061303230309010c0311010f1d160312050d051e1f03150f020d090201090b03040c0303082815150207030602070804120c0305060c04 67
    0x2100c03070100412418110b1042c01c40d44900051464162201c000a409401c001c00768198000c1894061041145007811203400d106503900400013101207610166903403140c80e81a90402c08400480d00405003e04d400510b00d2403040020703c900300304041d001004200748101d01d646600a8090700503a82c5011401014a00007122228140b030b007140c9645c03100340d0b414250a400c00c1000c100b0000302441303902c900c9000701da8182210403840e018550300051800081d00400301c3d05c0c58802101150400403642c5802c980e803110526180c000c028002c0d40040c80542c0c00f404249000003082c0640c10101d50020b400240b00f40c079031640d0151202480c160b1404103d4008107500c0000c0c4080c40480e0103040b906a00c40441e4414042e0109080220741a000d030f4031029007400b9403a08000c0382521040041140500803d140340e09182e0307a280c3c0029907501140c0310191206034000391003c01c0c03184202c1160080e06104004221590359482c01440000e100d100541e00e41c0a48008504d4000380c0720115030032030745 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 917332437 1250 917331187 917331193
    0x21b3c010c02160f0b070b0705161b0e0621010f060311090c120c070813090903090e060a03110f04060602031201080d0804150608060c040918020603070815060304061b0809 75
    0xd03603680c000303464101038454803e02805018041c4d2b0100d0126000d9413607032185180c04200382000000e00c0070704623190454000c00080408000107030300c0e4240c0107100000d0080344a40f10031482000300c4d004100c1489580d00c3c1f141080342c084180302085081070014401a1030040c0c0703070380c0d6102c0343ea40180607480546801c04060301c045420105048007520859000c0c002d45841c0000300c01070019921482e520a150868032207460000340b58000200c0001007429090003822480c0c450001120070005000041c58081d010007910321586842ea403c00f54a000a00b0400c00b043e10341c040a9541d400a40c0c000c1041d048000011542c0c035030200e000012203c2544407000c1a468030381e5151440500710700d881447d2070f500c0c140015044000c01c04070f03000e44a42c041a655a5080420000039110707112105011701e20aa96481c00584a00003100e0340101a46000b00481c0c5404910056610802c6401980311202000303000610590b0303801858416110383d9006c8200c0e4034907c080e106140c046178402e030950 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 917333687 1250 917332437 917332447
    0xe13030c0b090c0d0b010501080702010e03220b0301060203030912092b1a090d080105130902152116080103030f05040b0706021b3c010c02160f0b 64
    0x2401c86081250086aa8419140000140400704550301d1201c40e05440c0301d00301d480100429604030070707640d8000100340700134000d07042c0303020110340c0e01c0c881c0c809011f440e014440d54a65920380e1224010029102945000360f41796503d0310005c1d501c2e002a0703420445130252810040505851008030346d10701c05d01410644030007140d0b51114043d903a000d0490501a003004c40408000f03070003600304080c0020310035081c3c0c2d503500300083c0c3c5c2c4d85840c04011062060140600040c07201c0e0b62540010f480969090801041c41503031407000c260401d2481c400f094140c900860503032000780a65040180b20a03103280e0421199076403100707051548c064a03602034040354407000140b01080c4288007180c00840e81e8141030380350554807040800680c0c09140240e070003d0380031600c4448524040b40c1ca1001040b140c000344000307003502d803c040403204002000704500f10b01070503c44528410800b20220b5030710480080141100d03400001c0d440300d80159501480b40101600883d44298118a1304141da100c058403600300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 917334937 1250 917333687 917333693
    0x81b0a2f0a120225061b060f1d150a0905011112011802070213050405030c070b0d0e010605010f0323191b12020315090414060108060105130b0103150b040e13030c 71
    0x178010206c0581e0b00303440c41d640d524010504501a40e20ba400010301d0000d00007082100c2345951050100c000390042d0040c207400d0380b45400c01080c043c1c00107000d00340003921805a06e001c6006000c0d141d41c071052a40041804d24401d44000c05840c100c031040240f0260000362029420102e01c95404001d50048007840c030741c503001c00298005a4020310590440386040d5030740d00d00500c1c00c16240d0008407050000074083d92403034000d00a49207a01c158000a005141c20100040d0207100c800300c4410405503170b400c1d0721828510081e44804c43d180215400903407818030108008015030103a8074841d029061107940d20458401002da03041441d125030320348205110a10242d8084e50010b001c110078816031011290391941d440f898240528850382d12068426a000516410400141d020910380e0300f08400421507500c900c15100342c050b04200000800c0306070f9000580003817100c09088603125081100c0440e600113034900500c00c0d42d4a5000c4407001e41e0f209050540100b015410040006885101d80000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 917336187 1250 917334937 917334947
    0x106120c02030421060e070b0a0e090601140307032007020418032a02031b0901080712060c050c0a151107170f0712081b0a2f0a12022506 60
    0x9613034401c2c071002c103a00031085803003842c02c1420740040c00301ca800041c6207805a50040c4038840c030403405503041e485510780400064098460069094822100000010324251090303011407542040b801100003820702134010310703450b504001c500300e005030b150580040740940030400400f0741c1a40740d55043c1180041c03500010b039000030000c050303404601e840d03003810050b5424095420802011071700c900c4903000c20800c000590328180e01a03440b50704010b40030311641d071666140118481d00180e01081e07894101d231040760a4840c0c0700c48d44006015104a00d01001401443d110140100540c180198805807038000010322500d0b00c01041c1d0080140400003516044000d40740b020001c441c00d0703080450300d071640240f10108004400c0000c51590410403800d10b010704000f04001445082030401280c46005094000e00a00b0000c1554008a0041002e15207809002d808102c5038281c0d01c040010f841c013001c000c2c10710b85107000540210300c161b922903021072001c1d840801501d81c0000746145801420b481e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 917337437 1250 917336187 917336249
    0x9150510021204080a020f090709050f011b0f02090a022d0906070803010305070b120601030509071716051219230a0203071509090b0d06050106120c020304 68
    0x3041d03025065040030204109800790000380805030107040628000d104100c01e290201112510643c417110600c14283d6100301c8040c142d0360b094603510002068440185c40d0000c401c50f105140101070a6800100b040c4211140009813003500e808140351605c1c0c0d0720806070301810001000c005032040783c0c000541d000208001218101c000050300d0442c00e9008500b45030301080081c1c4402c41c00200400801004204c0040140755a60005050a02011101103035220143c0b44504140e101c5000c2042e0402c00e02c1401c0040190b80a400b820300e84025609480b8603601c504a1a00312121038001043e0400c80400700d802240c4030058100500c280b20207200307108102d0020b5401284440115a10060404280505995000c001e2459a03928030406203001c005401c4241d0300368202e80c6075600c10390003d1070034090b500c91240c042102e07003907000400c0380040c682c40f005c2c0405040c80000100240c1104040e48441d90450061100102c41d40c0140c0c2e80e40306901c11913641502803840c4200030031801c0c865103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 917338687 1250 917337437 917337469
    0xc04180201140f0a1d030102040f0611011e090b100e16030b03060106030b0f0d0201121d0a03090806090c030d030506040e1c03060f12030302160602070b10091505 71
    0xf410155140080036583d005640b01101140e03044001210076060328445c8171101074218020f62603c0d04164010340101c1a034496a801d0040398500680041001e4200c034003c0100940280701a2040490801c0500002d030826505103090101258000d1080c42446056443e4450b2038101d81e26601000c082c554405400c0c4000c141d5a014a00c210ba501801418000c251980c0e02181c03c480c200308002c0010820351500b480741d0f29500b412001030360050300340c0307060b8a2031120000c0d2a6004081410f4214030303a1065070602d0182c0c0c0a12010580c0022100c810746e242442290300982c0d07400002580c500003100507590581c0100c040210ba1842a00b00c1c0303a002c8400340c80030800020801c02149007590000300306c800b4085105248008a9052041d0401044c0c40d42c00ca0604034542007840d0041001404050105500012003030710114503000b0b010381c2c01b0361201e000c642d2035101c2e003001145107900b600c601c2d044c0c40410f4070004e4022058080c4580d041049500401e183d443c1504200400c00c40b0742c059 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 917339937 1250 917338687 917338727
    0x2040915031e02180c0307090617011502120313140a0b130c08030307020d020c150d02030709030f120206010e071e0e03030c010209120d270306050c0c0c04180201 71
    0xc00110100131108500410302a2406500c03810118400f601e6804c268103c0c2081090003050305210f0440e01d200c20381120511041d80c0103030780032003208a0070050cd429000080410001c10b01c4410300c1400c02c1854000e02440c41c45d1400e81001103010b44900d00d150020703009040c0d000100d0100c0313030002c0ba2f91103e184990100c004082d544c2c01810300b1a0402c45040001d600048070031050640c05014039403c51004944110900f4001c1350800e01500400080820040d40440040c0a640c0142c40c124080c1d0381288142404a04926080f0318103d0200400387c014040c0000001d000003100401d1030250035580c40381d108088004085148100700d0661000c1000384495001440791801c0c002855820f00034000540c4d520808402d104031010304090380c8006034000556a209103501100c1d40600508004000e807590321060090701070b85000ba000585111315040910130b0144038100107040d86880740c0d00383c4820380e0310780081108803421381c0601900442c0c201c484030010f6210382451507005403c0c00e04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 917341187 1250 917339937 917339959
    0xd1412040f02040b040527010605120a0309230f282303032b0c0f030c0c020306010b090d050105041101090f03031b14010e0102040915031e02 62
    0x8541090000e55040d01c26a204600400a41c1014019208180c4040c1e8060025003410388802600d65812208100304090380484000225000e40210009280007051041554480c8503e180c80f6001e0a008401085000f4000180c41803225808136070341446840d00041048102c050040b0b149400c0b11241d8031507400c0805112107040500086002148400203815040c05e14040b0000702107040200d2400c1d06403214501c50700d60740001160483d124600c200240350400c8001d24410000352a41745500d64101440144075551010940345e11041c259030a00680881000030b0f5400604104065090b400c5680103101c001129002010100406086440c4075003403a241c550841d2019202140d052000550014041d0390000c001009011140c500c0d0718803c1c1303550b40152880d1000721400600c0c17010724042d41c090060446154014420080c0203202c81c03c80c541c6058000d510500810706000e1070016002d20304182c03011a04103880d400000507800011164110603c40e0580e08100d034043c5808030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 917342437 1250 917341187 917341207
    0xf030a020a06110d020604150b2202070b06040b0d0308090307020901031a0f090307110a05100207083003100308040e0106030b061932041401020703050d14 68
    0x7040c0002000160b480c0203000701d0007aa06030506020300040e000b1540403100380008950f4441544003c02d9440100049011001000c5806080206c0a210100b001c0708419504881030303800814030248034001d1401141d590300200401c40380810728254000301c0718880c1d0400240594045500030200c501100c1c20308004d035000401e9080240c05c00c8030303000c04050800500b880b5003445650005000101400c01e0702d080382c2d140e650780c0a140c00c0940310588000c0c0c41705040c1c95268031040070b4080603181003800b5004c400b020399580000d00c40d01c98903100da41148103c1007511805c20035000c02c450314090a45c10801076803013441d04060410700711400c0281001002900d8000140000d01603822154020b6240c404094211540c04941c00d004010804c03014a080c00340041461031001981086030200200030b03070842f01c840d203c0b22560407500608128201c85481c0a028208a44210305032168a407654401203807580b0203840000d0007a030040083d010501d024100a0502c0006d80f2006400d00304404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 917343687 1250 917342437 917342449
    0x11407230d050403060609090201050d0c050f0c011b050307020307080d2309010c0903020f040c03090203030423060a020304180f0912120908090f01022b091406090f030a02 75
    0x20760080c040307500000c1c2041080300070f00843c80185205001041360312555000a041440ba0000010f1000d81d1411142409400350040d180c0c01103070599000c0d00d8020864a41340203246200d040d1696603410b85400007044d1050301242c3c80348000b9406507041c44001d540700b01d01c40e00b08580c0900c1c5a610303080141c0a0b0b4000452114040c04003003000c010900b449140142162000034683c030400107e444180050b032520b4403c20700644054400203000800007808034014502d80780c00944c50f000000b000034002c90390041c01d401d40d01c8144089801c0b1040c800400070148605441c44001d60000d210802c10101026141201c45010722400b0501c0030808050004a8010381c000b1070300c042c20442d482c00d00310781c851841c0d151106190b0080101441c6900d030410303203009520b12684101c861900405a0b17910030f11050392070601c02c1d12014181c5050a410040c078196079507200d0000340c2040d00014501c020303000c82c0c407075050001e00380c01d141c03149600500003910312070201942c043c85203022040040e20340e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 917344937 1250 917343687 917343703
    0xd0c0207050603090312010b0a0e06071511090109050f130e0a0f080d0c0c0b010b0f12010b04080f0a0c051311122409011e0f0e07090501140723 63
    0x4d00b01031681e81090385000b084030709041c1c00c0400311810501170507651540142c052408648100d51050301d802d014074110780d461b00007000c903640035400d1070f442a40284004000d80207513002601d40144403500c6505100e030414990104550200003c4514001c51f00e65501000d0050301540035190440d10b26151148200268841164001d100180100005642d0701c40d40380c4545003403074542d00d40301d43d81c1c4a603602c604060140c1031520100003451036445154008843c514011555122019a51114070400c0c5410910605240d4000ca40e0180403d510104150700926030211000d0007440c2010180b12120b81a65150481c01b43c0c0d401000d4040111038002e0088020000707a450002d1402504010102000300c4040030b1a0039030000d012040d6480c500390030305480c1c0100c00c6c1c01d804810000e1040c1d81108580c0007440c0c140600d680498054081d102e0030344103054584400c2c0591380d0301e81c01114151103490200d90307801000d20054000070079880d000c2d15800031220b40781401c031501201e040e00785981 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 917346187 1250 917344937 917344951
    0xc0f0307060b060a050a11031903060f0e010506031b0913090c06021b01080a0b1504030c080622020a0f080f06180703120c0c030f020315010b0d0c0207050603 69
    0x2064200c100980c1c0d019401d032042c82038441a0618541c00c40c00313405402500c5100c1c0501500305030400c203442c401c01c00c1e06c00200894441d03107414000050040c2c007e00c46400341e4642e40c1d11030000843c04107002224039040f45c00145c281443d541c2ea401002c4141c0785c48000f02083c8160800550845503599071200c1c001d108001c4000406100c02d00d0840e03401200c55200500350b40042c8110100d0003401081006544028200441a540d031070031b261006211038420780d548100d401c0c044181540c031810140003907030320a023402d520042c0c95259150b50703460103d4060402c1800000741f283c01d020320310340f040c40340e520107460704007001e03190600c4640c00e54080d00240290fa1100e40442503005040008542028070391341c60340b03a503100c440c24480e1107008500001c2d10503d03c00c1e8200d004180308044420080d604122286922034507407030190035403030000b036081c0d129126a641c55440e025807401114103c0307100034085131400c01844c2d084400781c0304034168101580035042001540e510340c6801507101d014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 917347437 1250 917346187 917346193
    0xd05010f0608090d05030105040c0c0c0f1a0f030a0f0902030a05030c0d0c0c0e0601090e0106081014090406271b120b2701021c06140916050c0f 63
    0x704000008019000080c80c0030000c1d40f042c60002c03c642c0e080401c0302d0548100740d030b012032490b2001c0f00031760381d0492114000740b0401a0500004000a03560344020a80c0c05030141c00c403010540884c81071081c000e0408202140a007000460303002d40701e90b840050b14210245010540d28440d800003820b150f034404c0166425000000d80c410003010500103100340000d14101010700b09220b40b19a4100705d13050007101190070140e404510030342c0c02130700740500a00007003d10945660b15075400400e0000155429820801d40712004a101a50001c0d613619400f0042e0401905580340c0d20f8081c0900385100600d8050120000311159500c2c1345040310b59814014100ea08100c2c0c0d502d00d0300641c041066000203d207000344000400000c00c4c000e290f0750016618180030640c43d5840460110440000103034000e198400a02c07040d202d20030420849441c0060304003004000d0380e6072044441000b14410b000d071300603120000124076041c0c44040002c0c0c5940c43c6491800d2085503070b01d262500c00c840001c0602a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 917348687 1250 917347437 917347439
    0x1209030801050a090608070326031609150215270c0f1c0b0705090a0e25140c0c0405040b090c03010603031407050c130204090e070305071a0d05010f 65
    0x42000c0140c3c00051908a20400c015884d1209464607400f00b80401005540c07a1101100c5c40c0721a81008100342041019a607901d040c81d07400030b1111a281d401d081c004c20110344002406000c1c4446040c8001102e4028103c0c141c550542c89207d81401811a1180c0805d40c80e106001c0e01c0d001d043d4100d0010000c01800c0b211404000c000e041d03580a01018400e65643e250101811200031802c50354a41c0300d50210032030340780e001c01918980583d140e0107402040b200000907110750301048240c085d01b541d4201c00302c2d417805c122284034103181d00c82d03441d00402c0d01003840a84034200b280c0207081641c50801601c10508a80c00024162581980d040d210082d0741d10901084840511224070f91040860007048410f14503035011305030320f8100c0e5003002005408540c03d018810140002d501f510350041602c04a400f04401400080d001801406a110f20300b000b0041c0b40c2c8000540501501c2c0c210300140300300d503e0480e00a1401c658020143e400e42402d0040c41c84172180c9010301030281401d054520906 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 917349937 1250 917348687 917348689
    0xc04120c0f0f090608010e0d0c0c031a0a0b0a05010f0c2108042f0f0f1008091603020a091e020a030605131404060f020408100905011d03041401120903080105 69
    0x3540b226003005c200d9924290004140072000501c04803404564144141e0064060921031410745141c1d0018204030128807810b20b08258400015101d080028001c00c0303500155000d20070082d4041c021540400d001c1340e4000c05450107003c1c01b55500c0d02c80c40c0b2a04d90551031241c4143d0717252481c507411000c00c0b002014001004030100d04560455000d01c06018a4a20f000d0b8102190810500590107155021030f554200d4030f6104454182400140c0306e00528501341c100100442d4080380c800b006d5024403500074031040c000307400c42c0c3c080740c0c0c0003028010344608281d00b1100800008130315a144402490100c1615030450024112085281d00c00041303061030013041c0038a4841c0e910340c41404034a411683d0016074620300c2c580d504103030844c0d000030b4100c2c5182d800000920841e0070507942407044088800301514103400c4080030038410802400010403d1414610801c803030f05408103a501b0610081c40203080c5903050200444c0305150240b5106040c1c0e11035400c17158802026400034400800501603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 917351187 1250 917349937 917349941
    0xb150c06160f120c110f16051503010504150e0903090310050c0313020301180c080d05031618050a0305030c120a05040326030c0a1202030c04120c0f0f09 67
    0x405036035801d2030351a003040144000d003503d1107020781c402c01e29510041c40d82c0003403040c1050341d00000d00204640140c09182c007a40d54405a84224000034405248040b40300c2c10100c000c3c3e44681040d02085055908003420030020b0044044010742a10141c0400541c90880c0c030403980c081c0700c00f013000d156a00b400009250606d0740da04048401141400140314560361804112940003043d4400101101960b100084c0500100340000300f0b44500205281b05000030007162104a6209904560114150301000e44035030000711008d004d40c44282020202c200d0203046030102001c90b1600e007841c41d0340ca440000e400311181c1d400640d4150310210710072000c1d407410000c0c02d180505190200d8104075585000504074821400001e0040036501d005c4100c1244401484160708040c01c80075840b850301c29004c0210b90040910100055807403006a0320845540c4200da000380400c14080d40b0b041d05001d6031a01c0824082c408642480c00c3c03041c001000000194070fa00900141826442e04d00e02d01851070301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 917352437 1250 917351187 917351221
    0x1804291203130e0a050f0f0717070518030a0c05090a0b10031a240c0c041d0714010801330305010f17031e13082103040210030b150c06 59
    0x5121450305051142e1020443c186c19480140c3d4242c00c800c55032052012590607003800250310750090103209124946070010040c2000e40c0c0604498840b10455808142e91032610030000341803d011a00d042c00341e4105808039641c05124000c020555801c444007007065400007482140029130740350f040110520030916800f4442c0c50440d90301d41a8001c05858040b420490001000c00380e000095a0790481c41c240070b0060b209000403c10001c01003512021f90103c2140d044007801ba02501300c0200e00a024086940421103042c1c1d41d4040c03581c00d1031809154540194040110401c20940c400a01560540b004140404a0382c0c0440e265240039070760365140c2020f81040b0400e81402c401c42420030000000c0c3c1e1010182d20112205050705101c00041504c1003100d60b1091004408020490740400148220000106ea0b0380b00000440301c102c1d8400c5000944009601c41c03c0e101222000d140310b9040300c080080c0041924005070030180650030300e9402a41414032541100040003040411984051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 917353687 1250 917352437 917352451
    0x109080d05041d04231005010b1201060503091c0c020301182d11011701121b080d110c060c0a05070501050c03041a1309021804291203130e 61
    0x10f2864100350365107200207000010380b00085401c500143d00c0c1000100580e188143c20000c0411065858a01e21002d60740b080d21480007801d100c0c400000c14a00c40c400b1640700f8012030000e03054502503402c030040c001c02034081078802c01c4401d009031005640c081c811100da04034041c500c80d038001c00501c0e10400c018444030220581e0000c01d400300440c00c005440d41355445901240d00d6020000d400c005030b40c00c003940340d0f00880c001041c0c000801c40d030746080c40d100c4445003d501c1c0a0b5a059030301201d0303520032010340030f2a0580c0e040002110b002e14003a00008107a80c1002056074440942d42010900c0b40d0003400414050f580200b51b0f6109000e400c0c402c480140c4070038a4035a1909500e02d4503282d0b06c1c42035103d09010b08a004010724a40c00d904003d4403030840400d04e0981001e50f488540c0343c0a9004810041d40d101e114900d04012440c1c41d100d180400340b0404400c8000b080403001a803545100c0e18001c0c0e400c050342281004880304140b004001c01c94020700c4114440341408000e10310f5400090100d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 917354937 1250 917353687 917353739
    0x606230303040503101509090818030718020a0909110912070308040e1315090506070915030c110304060915050301050d0209040609020a030506090c1813020109080d0504 74
    0xa03c950f8401040c2a200104400004a000344890b0940701ea1185543d20052030180fa00038580300304411000200568008400074180710041201056203500c0c441c480d900740c0864030399144c18a4051a0003034440d501712803c0c8010100e40d01c0d40300700c2c2039408441c0c00c0f800030440026070b075501d0319100c07801a40f08504c500c000d1590505566400c1c50307520443c0540705180048600140201c0c1c190140b0390f22072a80314800703400e40d040c1c2c041210083d00c1103a20445040c013941c400500030502c1281e045084904040c84d0001100e840740e0241c008024000b9448100400d8103500c0040100410007000189201d50710491013503e07142c01800906407a080300c030104079080004102d0b554508a1040d21603404840401e038030384492400200030540c103034009422000211000013800408100240b199000909580000b110a002c011816014a18100c612410f80011958000c04400038220151060400b5210642c03a81511031a011032001020002200012b0501421180e038402c440010660509 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 917356187 1250 917354937 917354939
    0xf09081c1104090209060c031804272628020303040f060203061816020738090613050123120406180c03021c0b0114030703060623030304 60
    0x100308080e102d10702c248180941c000c114802c0796542c6a00b1140100c00f003400701d0f40d440d5201c0c0103010002d00c285250b14440d40c909140c10f15034500b00c0381c4035441d4604070300541d140301d00940e40f0f041001e40768032500c06c054600303104420803240f020710040c650b24080740030041c046200f0110951100030f0440c004011504244103000004040d085c40c2e078480c9504c500007588030303600d01c8042020382c03844442d2b0809460b03481041c0304031401047c5400c4030007102036090f282c17526101d50100700180e40c41010820305505003102d000d0041d0032034a04281c961406251503150503840300024115400501c1000741244550204100e1581c01112403901c1000c4001002c1454001c50400701440c00b441036500c0b4203e002c0c0001501b08941a03110810b6015a422726007400f0480303080002c90040d0034002240603119a811a40c418034102c240c83c546c1d80e40c0000140b403203070b01388020100a410140303507868140c495243c0c044001059130040740d019001c4490100343d01d10b100c5280c1d2581c0047c1402460107a0800c01c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 917357437 1250 917356187 917356211
    0x307050c0406030f0f15061217041a03090c06210f010b07121101110409150509070f03020702060d0c02100c0905040b0a030203010e0d0801140306040b0a0f09081c 71
    0x21303051101c3c903003051198400008034209021074035644840340d03864901d0a1030204000485001c00c1d020b50b4050400060700110950802d20f2a00c22400f80b14012031807071816243c200b80640003154400494800c2c3c2e60b945404202103a5190461030040002104040b1402c07400051000083e9002c01003a420000d103500d0304034101c0340b500c01c280000d40762400a0118a10650189982030740e015a01c5000b08040000d507001030103150440e00600e001c440c284884264220707003000d031040903920018103018040d11058002d85000844095050501d6003d05c0f0100c0940d9410003d043c85540103507021802c0800604000d04240da02d40809020341d107845070600140e680700101505860060b940001c140c002030000903070804090340000e625600b410f600042d00c0001003484005040161101e000780e9881c0c40020601c0c2c05a01002a01540604c00040105645101d6260803440d5130f50002091000c0702c200c00c00b91410200e00ba034220900040302d006110610091081d180c82d124420000c45407150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 917358687 1250 917357437 917357453
    0x3040201050a110604050706230d0e2b0306051f0f0c050f1605030714152703161a131d0603070e04080306010c1e050307050c040603 58
    0x140010381040300108180d21010b018110807550221030038101c80c0d45150a1038140c0e681d8209014030b000040046d50006408414002d5403010300c042d8584282c140300c0d04c40016801000640524041d500c43d0940700c181d441640848140c52440803080c20082c4c085000d0084d068804036031180c0d02465562640724a41c0481c031000311661102403900f1000c01144031012900c0d00b0201e0700141490080c1c41070300300144d200248070b008003580001c451580561360000c00da03c4008610401000c8021010382e04041c1c42c00b18040c001d10168001c03c00e0400110003e1030141280890b05540c500110b074040200b286800c10510b1070421840c070202400358180031076034403810305111202c64041c4011804c0d184200b050035a010103049100c011011035524105182c0b541c0c0030564000740a03026005001c50320700c019602c418032076030304507407000e165031641401101c01100e5480152881d50b40c00204500402016500300c09841c0140c0080d510303002c2d1410040d0400061501c4140310b0f0b840d0100c104001807001e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 917359937 1250 917358687 917358691
    0x70615050f130b030c0310140c040b0a0503060a031211060c0310170f03340816060b06030702010906050c030603060c0d2d050a060605030109090201020703230609060c03 74
    0x15001082d02d00031000841c1c45d05015001043c0d0502603c821788064524690206070014100d1002c074400d501d411007403040314440d6000310f40011001300148841a0300480c025604004043c0448403510382e00e03200c5074034000d91010007000190314001c00d4a0307034844c100200d0380c020035000b800358518103081e010810040c0d118802e110b408900c0c003103d0000c0703a00911180c0306210131201500e40d42e45040030820043e22280b107107070b510007118a06030649400d0140400d2481d661120782c540c07504e200303004031200210744048125101354840e444c0e00001e07241e0708003642c042c040c0c603000892100e0741440c0260076200020465101c13800c080c03041102a41d0001070150700080d45c602d91540d540318002c10000940303100c0180f0002c21f10740c05400032410f80c1154550f01401c162200400c825150700c0440c6050301c13224032600001800910051040c801d141e40004c401c903205004540105540b50794800c0441c40c2040c800d141121400680d10407844184031140d4041c400e1005000c1702d04d08404803c500c1d000c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 917361187 1250 917359937 917359969
    0x309031b212a1e101a01020f031309090f05070b040f0b0c06010506160803190c080702120307020703051009030e060c210c1e010f060f0504091106070615050f 69
    0x140c4102c00c03c8002e02403205032a01c004003041800307010b07140b80c10326454815401000780140700e51044805208004410340b1242c404900d6010303041480c050045c2c1c05081c8240c000c0c0c0c3c190b411582c400300050746c1001207038010006039584680300e40c80c0204441d580031090b44040c401d42c0c0704002000040002050b11415160111a100e80311054413132841100340c03c030040202030303810010030300c02c2c10700e841805808030300d01e1b02d041407162810101c011601000d0548110300035a200c1e280a20421440d01d015684c4000d4a01c126100c20381e0f03d031946441c111400581c254900c0c4e07039208610030b0541c009102266148260f0360720340307000312142c81d8550350103d900004150f00b40700002100900c1080c02160304880051080700c910b188000748002d400b00441085d00240d40c81c102121001c1d540b1805002c04a91a1022805080b0b10b41403c1c00050001020b0407200420000769061051351450050203445e4050301000a03500d11800c0c03210180d01f5950045071080e65902c09010301651080c50481803020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 917362437 1250 917361187 917361223
    0x303040e04060510050d2a03050d0c020f0a031a070503070906180b0f030621030d150e2805010b0702120a06061202090105060309031b212a 61
    0x6107040300b00c03a4800c1300c1e07044035a205026100c000c05001c1c50300c000c0614040d142d0040105545600300c42c410702c01c140d1000621a41005041d14051402100c0c2440319030b0001e080c840b0380c24aa800090702d074030041d030801c4a000c40c15900d00f2505001965509074458000e0030441c0c914202080043c014800d00d115420401844540d10200540101100001012802c0c84e00c0c1e2035094503010000550011581b482c001c500d500c61035002000c41c00030500c4160600d002551400d600c0b81803107001340c14858070501d02900d1034200001c03880d407011b0740c152140f0014103980220103002030500c01c080604054420601d0b060070014409100b40c841141d611a604945059016015040e11130030074124440c007600b0325141410008400966400f000d580724800c40e800100c903a02d4508000c001d0106980d14849a4020b01c0070344155040d2100d00003601d0550780031100c00881816110515800720316204915440c0402c0030030a50542ca00e0f0803400c203800300e4404a13040580300c45113036a08010044012150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 917363687 1250 917362437 917362441
    0x40302060f13020d030503010806060a03080f07030e100201020a11160e06180709050a1d0106030e070305030d090209091f0f020d0f0209120304030309050607080d0e0604030e0303040e040605 83
    0x141102c007100d9070482d40600003010605550901920b140c00921590070240100c40004a951801c0c210420a0325400301d0480e0030182e68010441c0503400030710084050010195100d0b0345a0747d041c80182c080c5000341c1c0090307034500620600926581200c140001c8540c003858450f0003030701c07507541c1c0d040c181c540e006220841d690714403000403460300c003030034005042d0090481441030541d0700c041000c2c107860050342d5248806a807a0035425213a2070482410030b140003681c0041c0300c203511130380001c655510001c0444070020b0701c7e0b072100e03030641d44201c841a09030f40d81e51580c1d400b1802c1c808401c80d4801d0042014000c0f00c03402841c0e2401000c40305000c074498035500c0c2204850100e09906442245610302c0302001618822000f0600030340c0a01c2d01d452040d92180602d41c20309400000326415a94142d03075103501d061500003070010380e810114040b5040360050091441081d0644519010301d884031005050707504080c18040c200c0582c0d0360300d043c040d8104220a018008001c14403907001680100c00250f01d07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 917364937 1250 917363687 917363701
    0x40201080c07081b0f15060f04110a020303060a2304090201230c1b030304090903020a0f0b06100f0e061305031f0e0703230c0622050603040302060f 65
    0x610400c0002483c581010a02107072114a15051100010310700044031070103c1500e003026500d03159181d0541d02c0d180b40300b001440e02d041c201c5542c0860040900041400c40b80c140c000d03100e80d0041c480b1000164000300401505142016540f0001c07d8100603a402807901c45048070010040421074901582d120380b05102103921410101c104800c08050b046940002212410714542c0b05143d1440c03107100b101c0081141e015050000786c801d04006004503e000c3c500140003000d8001248250203500409180c030000c41c0c105000c1424992140b20307580710314941241002404160208a02c040140441411400342e8000c1d01e0500342c0c2e6000c9a541c1d40312502c6c031094500d107800740d41015800d03002d41a0008640c60780c40a0820003401000c00a11050158041c1e0719a00c4500707100103880c01c1c113002c0000d84d10301103001b9050008035824050760010448440407030002c3e0f100c100c1a40c0034040c0246250401140049044003a0004a0740c40340b650070b141c0c4000350b4503d07014048610b01108080801c1003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 917366187 1250 917364937 917364961
    0xd120c0203070b0a1e0903120c211106040525091a0112091208091c0f030609092102031204030509090106020f070b030c0d060f08012304020108 63
    0x41a801070860351540d031039804031401a041a044c01001c01d50000c0d07060245d01498407000c2844080b551140d0711b180c5035854900c01c01c0d11a44502c2d0501c4403908901000c0760320903180400140306904810385007081d4078002041d81c0300440310100190004018400001d01c0031134040c2c0d000d5410f042011102900c001124891003240d840500c3c00f45c07800031407410f0040c903e000c8121780c40090702d600c0024860884801700303588985000900441d10718003089007642c054a481c0f60000040700031520800070210031480c50051304944840464641d1030807045003a80743c010032020700b001200078002c80c0c8959680401c4400301e000d02c100b0030151080a000590710800c06c4d1501c0c00600303103004481d42801c1c00c02900c0c0f58420038205001d680c04600210b016400041c658130b035030454034000c2c10304918102e58450540c08c00340115207071000401074005034040c113010341800b400c00c9000702e1491500c3c1101107030855030448030b01c03c040e041030014207004d03484200c2d201c0d90140c0c082c00d1140030b942e100340070105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 917367437 1250 917366187 917366207
    0x90906160921060e06090a06050408091c0b090304120f02041107080c010f0b0319290f01092c01201306080c040504091109160201050705090d12 63
    0xc80c48092595101c20415000815040700e0042500304504070134210701c035445500880d41200c0325403000b4008400217841c2c2e849613034440d01480c400c43c2440e0305c000c0051800c203510340400c001c000d8914294001d2001d400c94841d00410390f00000d5281c20b00e007000c04100101d50b400040d0400c101310301c1150964480d80c0000003252a40011680d8541d85864407501c2d030341003002d555600303619001007415040864880c5009d1000c0c0140144912941d000d4507000a02c034130401100c158040701c0f10900d01282c11000384111241030520f0304028542512887c9920405a00103140c590404110485810090604020110a90684520800e4182943c50150041038043d64541e5002000d0102041c0340501428110b02d20820034194559980d00c00c807403005003583c0304106200200801c000900d001d81c42185100c0c4170740b20b2008e40031001800184c40e03000494141800d1007004000c11401a42071045a0344042681021401c199407840440c1003070180c8040202081d916000e003240c513034040d240d03941c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 917368687 1250 917367437 917367449
    0x3080d0212180c15040504050a0e030c0f0115050604120c0b0403150513030e0f010c02040c020609120307230c010c0923090705030615040906060801050909061609 71
    0x20103600700008280d200401980d101c00c2d050040c1059404213140c021840b9055407402d5114500781070401040200038180030f000070100c41c1d078958020b00610b90600c0035214001d10b40d00523006484a0080702401c0d106d8041885411300f00040e001d100660380c98040d03400352464400400728034100ca02c0e020152800ca0380000c003000d000840c0000030401254082c404108441d8000d1095440d05124030000703425200009012540b51080d0b03c2c924107000e81c503100d200d101490a021440e003190080b40484140030005401a04000301300172004004103e02c201751440088000e00d946030100004010b0301142c0100a60b41c0319445281030080100021385900c0c403c1c2600801411038a01c1c0c01800d0f07422180f00f9890803502d0f40001c0060f104564460314481180504148820764a0040842d00d075400200000e40c400c4a40007032619149551000d803026001071000040c2c014140500980a0303041640040d118045001c10004110404202140c0142a0310071401140e61484c0d011340c2ca610058210f5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 917369937 1250 917368687 917368717
    0x11217041a0918061e0102030f041d061e0f0a051008010801060602070b160c030f08040503010b0607080a18051008010513021315050d0e0d02160f03080d02 68
    0x30410461490003464851000c443c1007829210304010441d8010003201c181e070b88001c1e007103005110750b4031454248000a0051040e02d240c240d210100c440281c215030003000401104100001c552000e44141c16009041120309102662035580189288058002054005c0251280c10300c1c0c5a201d01102401501d001042d0000c907181503070780144031031300901c2180902e6091a1001402034000b0071000d06803654010350b1441e184580eaa8040e590b1310304a42110b40c6010f041c030010200c1c200d0868428214800c449480d5501e1602c1708260030340c0e21a4954500c00d450410200b000102c543e02140d03e042e0482c10a07a0819410350300c2110707414a60392003d9003040b690103030f08071000d0340410b01074162101101c18103982e80c01d0a007008124010844122091440303a0028800307a41403500c007a98027003040c41c04034940803510100206442502d940f019142e0300c499801031401e43c0621101c0006001044112401ca2400400c400402424030018040c100c0025205520914030380454540364021214 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 917371187 1250 917369937 917369969
    0x170a0b061201030f03090905010b0d200309030408061f0e0603100513030305010e06060304031b020310020c060714270306010305070617070905090c3c0301121704 71
    0xc555080411301c11130019100490201e28000d181c8281ea040c0d61000b00d01e941000c0ca0710f50058020402000d009030200001c2283c403150b00081c20096110706010400b4680703075840e10090701d1604802a140b5000350f040b0101d100c01303018580c002d83c002c4450700348415041f40c443c040440e042a68610303401a51609101c200000240e4604658a590b88a59020071003a82e9482480c8c4142c601901d20343d80c826010804100868418404010024512171404200404681c00a40b5140110b5500741d14140c0102d00340d0501d60b024411258481a9030070038010300e200c0700c50014041d01c2410343c0e6440380144030000d50804950a8402d10148101134119140f45d6103d00340706036511168419480000c0c1d0203004110350300c010400c4e55001e0092034035a000c04a041400f000700e68100113050702442c1c0d0381442000e00781c500214021316604101a0070a04444000084180e81c103504200c0c0000c1010410040210301e0382c2c414507404030350b082040390f010104546065103480c4521303441034410b070300d6600e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 917372437 1250 917371187 917371193
    0x60d09060c1e03050108030f0903070b0309061e0702070e0912070503030f01060219031b02090712060603060302150310080d020c0f0f0108180304080706020a0c06170a0b06120103 78
    0x801255050b001114000c1401080c42c001c405942c030074002d041c02c50700203001d440e40361041c00014019409006050f54183c40d140d00380c01000743c1044030b01c6a0658800c00502c01e040049a1071009003010995000c00c941c03a0040300070750b841c4200c0c072812050306046000940e40b0030f428415440c08403840d5550360340c1c5c0c000c076081040d9030382c106807000e03a0110b1003000005019800002d0140d08441ca003101d40d848000d8030f80f81681c84c0e001d0284100007184c041300000f40140d0381d40304904e03c2040240c9403a00050840345840c0120746243c0c02103c180351420800f44050382e908058801400340300039199580f550f600940200303900103680000d4292082c09240d103da00c3e00852020315900081d48c0348144405810100b04800e03a400d0603c0d03000c601c0b404046a4520700b80c850f50403103509201d040300e04e01943c5811007454420603911080c0160007401441d804c12005081a400421040c5017803d6440100351440a00807000780c4010340712613482c2200101d0ba1a100140e8110006046540004d036950b81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 917373687 1250 917372437 917372447
    0x809070b0f22030f080a0509041b030b121209061306050c0c0a051302090312041203180305031b10050f01031406090303060402090a090515030715050702060d09060c 72
    0xe0b150410122005044000c082d004074441070403a50040b00c0c0411030001500d94020340c0c0e0144140d00c041100405c1401c1d040d446a010780c08100c58500d0980340360385d092000083c1155200c0d0340d824070801100c2540b40028200081480b180d25503d0401a0303690181ca00046481c0b084104090384080c90707890000350345401c003000e849100c40d10b030192000c9900304020014040d0450141c075510a0401e1900d04095000f54080c00603594040c0454880399024114101c00b03422692103550301030301c203c0303454040541c0011000300e80c48601c80000d00403411a42c0f615120b0140034035428207200d1b550300700b440d501b000b0402a950710402c14420041070070f0039420750704465000d0109030303490110802201c080c0e40c1c000403510711a0741140301460845d100c0104010295001519040c1d04c01e00001011640a2007031140c54060740d501066041c15102c480180b501b044030070760005161000c00500c02c0501d6800404403500d140d811500c56560b07465030f00440b070040c00030340702c00380000b4540440d440c0c03c15000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 917374937 1250 917373687 917373697
    0x20c0f0a05031e28021f32011208120a1a030c2409041e050907080a02010f0507080309010b01030f0b0307031e14160e060607030809070b0f 61
    0x24442084001608030401c003062058983e0500b04d0b01103c6419120030f01d000f07210030400e041c0343c819909003100b00040034107800c100c031114040c41a0f541c4800e00f8119811031032001650f000c2091407140c0030380a444101010014850310582c01e840520b03a004206800c000c56000c1d00d240b45aa203100c0c20035601c0c030802049c070103c0c001c6002d00215040c0d40107180c00a0784103500d00c4000c1c007942518020800c6031955410308030389190301040500c14071010f076070f0b07502880c03082d6a55800b541040b480520400b8094400250100d402600501e200340031594010604040141d0233081c041e100c0599210200c447d4850840d02501d4441d0103c24011a020b0641252032440000d0768180303c11460a841881120003c5d203e031030f4158848101000061452060209910b85005450301c2403440d079110310701c0802022015980c0e80e00001c0448801005c0b0241c0303070b4060b044c5401c00c40d603245000004180188110740b009001d0021010014040d481300700304000c054040b5607001340d180d01007072003030401765040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 917376187 1250 917374937 917374957
    0x9180903090109122a0b0a02060906060d120c0302030d020a0809060106140a0c020a0902130e010f060806131d0a050729160203030a0819060612020c0f0a0503 69
    0x9810f0000440c041c04805858520f074100140d100a80e00c86110070032240700060013440d1a0103c0800000c1100341ea40142c608051560041c0c040b40c5049201c0c207041c50402401c82d885030001c0e10080001c98152546036210342014240082d0341003007414141d295000714041502043d000080e40d2202c2035100804500424007c011180c071a41c0f1048159003001400d41c0c90b000308401880390303025040c07080c4c8400d01034500182c00c02c0b842c262078100f0b01c800c1e64845c450082c000003051001300314030f03031502c000240103040d00292042c0e450304041c0c00030b1140401410b142d1180c441212542d405070b4440d44940607103c2e00c00d0a1051160b13184500644410200f441511540103041c40010a034040300d260b0040203200400c446543c00300d0015442464000a0002041200d044103180c010b880810041c2040c90581c0c42e288800d19010006030440c0001c030741d480031080c1c2024010451503412040c2140c203000c2c1000e0250b11400f00c5140545007032a405102c282e2489842841010b01c480400106402c011f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 917377437 1250 917376187 917376197
    0x240d1e1406010314060f0a03060908091003020c0a0314090d050105010915050d080f1312111807080606132d080601060f210606021c080c091809030901 66
    0x40c45100650444c1c04c08610501c03c0104080007842030302e49113010700314408004051038055a200c2d110f180494407420002c6900810000b040c2c0c1480c0392000340c2e10440d980070300e010351074240881926610307070191813801814001c0075407800c02d4101c16041070741c903401c0e0040c103440c03961005414500d01801c002c0c401c0014462400301003454003000c25260320140c5801800750a1103a0283e030780c5408540c800d000c4a142a0018000b00f403c0192100c1c404d002440b60803d0000d00700d03042c0c186644000b503d10380b400e201d0400c00040c015810317600030300345a200d122800c180007555201004a1058414000445e181ca5091140401c003250b070380b8210200b03507000041e0035072403143c0c0c031075000508005405441125880100100101d41c403a03c003031034920b907440c50000000405191158804031165012907411600c1d4142400800d42c10821821071501890454214400482c009030100d0009840341c0216400014980d00540300c2c42615410042422951040351038107030203081d12600182c460300d002a03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 917378687 1250 917377437 917377441
    0x606050105091c06020c160302030c041b0c080f04081e0a0302100e15010b19021c1803120809070e220303090206040f080705240d1e14 59
    0x94031400030b5452036a406810443e0b6030f55803001105036001088421504240c0801c0755120445043c0040c0c4d08076821f60010082c06415441014245541104850300a174582006004c01418030443e5100302005400c0030707031201c40c89041201e0303980708001c0c40c040c2e000c0d400240051242400103000f041c01080b0701c2d005c1410b090108103203450305040c0f84040d006034803980c2041400d00031940032000400c0ca42081300c08100160102d402c810400740d200030703c001004100003a6005042d00c4d62002c041036480903100c0424940007030b440200c5804060340c10000040004186022a10540005140c21000519501c040d40000424000044400f51450700030b400f030008086904445e8107003e07502c01024898002d01310710001c405104555001e40c10140c4841c00b00707015898010090000d8070540c9a0300d1907090810804c107141198943c0018000c2c01c2403180c13081c2001001e482e1600800d01290020790750342e00c0740003800c05001c68461001450201b200e0028407404642c2c8501d404012455903500c480d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 917379937 1250 917378687 917378689
    0x1b080708011b02060105060f0405040f0507030c0e1f1812140703080406030e01140114101403010905250315060503070c021c0b0a090302060903040605251509060605 72
    0x207000c580740030700b02580c40680140028500440501400c40c0c0130b00321076003061380e20750000b0f05568440c080c4418640e034a405101140303905009001030700d902404c00c4407096840030081040012281c0da46207071000c081002004131441004030140900f1190401d80001d070311102a010b40d00f0084204075a51400d03001c0400c001e220209070365044a4000c035086082a1801100794060451802d50f00125503071395002d0071900c00b1110354a03004e0100050603071619009402488a0f410300c1c4e6940d0f400740400301c004656444420422a81500d424400200e42612048059060071090040c091900c1c4280c4031840c500036032681c0b10804500d460076070518800d03616001600d09100036180381000424904a0402508081c200100201034520f01445030300c0c8151202c1d40e800c0410344507241c16689a020007410306034100001a040131595001d903203001d2601d0b83c05882c6200c0c03100500c03490b880030030051420450395102c1c00d4042e500600c0005400300e071850300000810344044101ca82500d082004143d0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 917381187 1250 917379937 917379971
    0x50f0c010b0f12030414041b020a140a021509040e1e1b01020309101107030b0603010b060a0219061d06070201051b0a031104031a0a14040b0a05041b08070801 69
    0x44040c110081e40ca054103101e86c4881e0340940e0400030350029140c250780300007808440c40780c141401c410b5014158440300784c0f4001191080b42c40074814980e21007000440540d64240043c0664000820301070360700c2c40d84a002c9000307010596002c80e2240205010444510084c162142180050340160f80c4421074400d1000c403c8181440e03002d005078000e025074441801e155022207100251814901c005042d245100380c0307004001d4104030760440441c03090001e241424040c003c121407045450314103002d03003000025134480d00200d403100103035660130584081c0021584000401c0d6213180405101544407181c090341c40300e0030307504c0100661030040090b441401c1110f00d54111804070342e2040c41c0030382d8454201d0140262103003d1f00c4100c000c010000000b0071282e0108611001704004055500d8542207a4044400c00c01012082c002c0c01020000014210103100d0707072042d2000e50002c0d480c1c945081032000b1045d28507075003001345000720020801030300c001162800c80b44c0540080c00811000012124 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 917382437 1250 917381187 917381209
    0x111204060c080d111326031c150b0909090c01020607110f24010b0306131e0510150e03030d0c140d0203040209012112050f0c010b0f 58
    0x103010548407400144000d0000e203040c14000f4408901c0110701d6552400c190711884010070303c1144104204010202000071034805038400204d403e20820068070591244610020740da1205040c07048020407001c9980002c5c1110b03080040c0110494071584410b0040d030002e200c0d2131207250883d0000304001800038070a02e4444060b0b0103004141c5070640b056030711414401e0307065806d000340c81541c900080100040d007540d41045c500c40c0c8004030391009011030501c0c182c00140803210100102b2409131074414541c0407821450710002000074056041d0b41c120740c1619074103500c050611050045402030234290f1419500c44600c070740c0c240400c01c0b81c1039031040c2440c25200c3d0550400d10003110381d8000c95015280e085118201500000b50150340f074400365001804421405d6408030921055040c85010035024100c11071301446141c40b03004032006c00040765600100005040000d100c040c80c800d0040e036440e849155907141e100e0f50302c580340350b020300850041c1601403040400340c0715080c81c0c6141821 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 917383687 1250 917382437 917382449
    0xc03080403060f09200112051005012007032004020a2a030e2e08040b0a051e060102011503050a02100c02011b0c12031205010618060804170a111204 65
    0x7030010241c0c0701451a041171602294140301c040741c4001100901801114454013007001d90800d5141410009800c80c0c03c052083c030b03184d400030381c4508060500000d840342501d8200d2021058890f542c2c825002c080000340d14250050700205004d074405801c0701d0f80200d0b00c2aa203e81d80003070031000032180d001840644c4080c0004100d804540d07450705100217142c803d00080461000d1500101449040142c40e0300b1440700090750358403c20050000c5003c4550f0041000c0760140410b0920010f070030600b02c6809025071801031a00c0100b581a0b000b5031122002c540424400e001c496901e09055440d06011071043e400b40144e003014410540c440e8007481c2d60284d0503160070b001c4000b402200207448001901c102d644c040f80c290003042228108401e140c82c0c5c0d12990340c011110056070100d60a80da01a400396040c030120000c07110800810302c080406031503003442c0080c115a03071402c01c0c4c949240303075030103d080000000802030f0350f41c8e81c17140f545281e800d500c0049400e0941d60b17100660903803240380701d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 917384937 1250 917383687 917383703
    0x10b0118030b10030503030c07051b090a0e0c03100903140f0f0304030e09040f050c0a150f02031308060106350c090a080d02070b12010909020d0c03080403060f09 71
    0x92000810b2402d00980110311101003590042e1a03a40d1146564416980700403589404a0240c04011041144818082c40004415079208102c00400c442e1040a03144415080e280d60402501c0c200806c500c805269008003141d000c0907190451070f00074201e662080d400200d000141041501d90302c0c0803250080554104180303040c041e2403101e4695000034104604201c840f201443c4c0c00d0303940c104070600460240700d00809009051403e04c4c0340c8145c1180c070b2801a03140503000c00002c1b4941caa5182c0d0342109003070001c524106120124114425001d4081c047e290070080440c513034100044960503551a91200c5550100d11546400f9000c02161705440140c50301c0c2c915144030246036552904a0701c40b902d02030a1090800004626000350f422551443d808004a0803c00c0e60401604004003000e481551a1a500c11a21400d520050040c80485520b40c25010304540741e00c1d00030300416800103280301d002c07034884c90a48082e83c0700d0700c001d864290808203c49232a00c450b2141c62150396022180c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 917386187 1250 917384937 917384939
    0x9080606010c020310021219090203120d14010f17060c16030c02090f04120f2a0209041505071707270603021b01050103021014071e0203010b0118 64
    0x444480b1a1880200d0f0903008460b000300840c1680d002529401048020680540c98100300050a40642c070140d031341c44908084031540561030101d1201c0c042ea80218030780d03664113a048020f03000b0388180724440740131040304800040c0c01c0300c181c9080c000755408141000406000c1d000102d0b50f0784803d49001c180641700b040030b90f08012401c00d080340450b109050250a500c83c2e50002a01c511085440c0b0345990030714400c00003041000012450038103041c0c10708540c0004c10080040002d5840190581e46908000f1f29544041420540c240199402011f2103801c0c60545810400c641071150600728541c1040e0100e66603500414030030308007010b8075601c41b1883d170b20ba1404030341110316401641e4444000e001007c0083c0c03030f6501c01501914031901c0c056903c0c0b03c3c5200c83c00040d2175080e49281c20b0391410f401400103945414038081c402c82e5510344580240f05420700768865200c1d201000f098420340d8171754030720218030911140210034000c800801c1008a10801135540054142c0721040c00300010303070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 917387437 1250 917386187 917386189
    0x180d080c0d0f0614040b150702150c01050702030a030e0a03081f0f08030414180601050f120109050f090a1e0302100204030507050a0b0a02030703121803050c0d09080606 74
    0x54003010071048008545a03800038050300440c0c866801002c0c0096241c4043c0c42d940c00d05024201d1142d074152103c50400300c210b101030285009030300009106003501d0040d1601002c0d41001d50780e440034660004c1182c0e017800340d80070759241d00c50302a502c0402e040021130b15041c0c070042078202481c5d03090388070000d1a590b14503450802d00c03a003100c14658000d15071000700f007000c465489a00500514001140d0356420310400324440041c9a465611500c400c0480109008503030b43e815400031001c3c01d007240c44104002002c4400d001e0080031400c100c1440c40001485001c41c1c12140c041d120441c102030040e103e8040c000e80f40d00c50108040d290f6008210b031020301c51000340030503a000c0d0180c0b0640b040d40d42450941020fa9211b9403043c0c80940c07003188c1c00d124070f2609403100001410003000707062601001800103900c0e80504640581407001140c5044101d2006822035080c0c0a99500303480c02d01e80d5640f030302500384c1d080700070401098410403005007800e5018010800945d9901ca00070003441e03031440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 917388687 1250 917387437 917387461
    0xc1e080a080306010c060e0a0b0702160b0702040c0c0b04060603061d210f0c0601080706020a03022503061b03050c07050c13060b0406031b0c261603020105180d08 71
    0x51701c01c46040e595800705181c0c0480502c8001c1c0e40d81d1062100c01c145080034140246092074542c017010018028030401c00c00808010100e901603a8107460100308000c4048066070214112600540806888410042040b0441d40503405481c459081002903c00b00b240e0008810802d008580c100d40c07080f41e01d81c03141031404000704081c1d040205e03c14030305020510402080d410540c90407400c7e901c51360060080000901c03c1001411042c801402c41310f0180d10029a540e65060109850240219004460030000501140030b5030b040001800340386618401e02401400c003500703c0d80000e252501050341421110304035219942c000c0004d010b401844000c0268049442108080c640e81e9030f0000244003241c04080d000074031840c1c4001454060584041e4510088041c452040103900c0a502001030842100c41d05040440c1c003809003002c9005031680000c0c41403c0c90398815030b0408041c403040583c1504a648910410f018a90b042520310070101d03910307088561403102141d00240000d260103000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 917389937 1250 917388687 917388707
    0x702071e031e0501020f0c030c060106020f06010b0c0109020a14100e0f06031302040c092c07110f033c0f03070201020706183c020103090c1e080a08030601 68
    0x341c3e00062401c402c9240086460780580b4090a81b0380010544008280e800d0104500600c4c00c0d0018085a440c0c070102c003a1540d07014086e041c00500080351581d88514250301004003240c1c080c1406214544400c40c210460f81114240e03803042710241d03c21480b4510554845d540410040d000e0516a58424100811600000c08681442914030741d1680546d480d40500d400b21003403502e17403003001409c001080e8007546c1d036403064881130000f080042500b100120f500d141c0c03000c2c8501c1c101c030011041c0003405040c00c100d00c00030491848049880b0b101c3c1c6009158100560a084900314100d40507000318410708110885001820b40e014081005020300200046074840040e2000516001255540b88111000c050240c0310300d00e89031301000c0030400e100610b501083c0c404d8103510703010300d040c00c1c240644408103503051051131915480d803011640640c00c80f21915905c0303105010400d403038422400d1246082924031401000c0d12800281004011452808054000c070b8282d15603664136006560300a08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 917391187 1250 917389937 917389943
    0xc010c020f0402040902040f140d02041e0908040801061e140d05060f06090c1317100212060102070f06020705060310150e0f1c02270702071e031e 64
    0x410580c0000d90baa14801040501740c41000180c03034504003000100b0201e2540c214602c40001401341c11600d5807280c1101c1e07039081d0704881c04100b08040d95042d090440100c2c407844001c5041c08448810840d410003c0e000f601c81d034100802ca46076075400c400c03180010b0022407007a0344000c1c0c0d40c14041c13a0300076807800c080543c000e8404408000d09a803020300c0c0c208100c0e2103c001d01c3c3c21034140403841c03801401e100e800104441002d0300700562801e8251064010f0b1060b1010503a43c80080c806009013841000c2c0140001001107460b0302d41000c0c00307948141c0071114130303006020360324010503141c0203d15044155004d13940208205c6d0304020602520340e001820144e64806030702c0e00003540342c00403038810a0081141c0c1d1541100c0400c8000e00200182e2410901d06c03841c2d200411548a081216602040e1a01200c1c0c2e0400c0741d002224441c0312100c0201c110014922050030401c14980026031041201c80c0110f01a144000c0746004e00b0110b503407808001c10606c001c10b82030b040801e03d82105656680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 917392437 1250 917391187 917391199
    0x90a140103060308130306140903090f2107050a0602070b03130302070512101104080a0b040c081c02060108060606030a0c0e03010c03090c0b16082d03010e15030c010c02 74
    0x1483e919460455001640042c3d50080221014000c10542d4014440245e0b6803402d48140c1d401c04480003502c0b8021506005d0281e0b503130041c4600d0984d141d0700040142c0e440030500128212042441a81300d0ba0300340205401801078400c0040d40c64400590f02089500d0050580e007142c4440508200d100340d062000e0b001c603c00d596001c29140d6400001301040f04041e0000e0000b0b4400000300d030300b50f0340c076940210b003104010301042103007603000724003510580d5200c155040560b8a81c07402c00c10400d0300ba08080600c0c818030f19503817a50300c41007102d40d8031180070f074085410507070303031402c089030382f00c404644242d00079009002140103154281c1015122048a00b04600702c6426040030a0840b01e505a0450000e600ea80400040c016a554042c2c0a00f08218030715140004080e42180f2807002c4800007000c900b00081c04081c401d00d030b14103504488011480c0440e02404000041a42c0e80082c050300381440b40000201d40c0a4100c012401540c803c050064a605148d42006544200c164034090360045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 917393687 1250 917392437 917392439
    0x30804050c06040e010503010b10050913060e09010c080a0e0703082b0b150c0a170c010501081c030902010206071d0409051005100b0d0c0309020405042303090a14010306 74
    0x50b440d4009003028150044550500f0740c5800100b50a407049150498000e04121207583d494a0f03000d02180d0a491007a111010750405842c40e00008040d640e00030300303080c04490700b8040d038400103412910a441d0241d1f81c1e900c90780c035110000700c01c0b2000704804a41d02d510802e4104001070108000e045422500083d4102e45090702400d19442c031495001c00ba141d641c0c441142c030007441c00e031480b0040c0030000e410050a19844000f016540c25018070040c140b11400649001846491006c8804980080c0d000707003d603507075034004540d5401002c8940110f0741120351f20001c4c6944039100d4030300f506805a00900282c1c449807030983c2c1d41200540c2000d00c035941411444c8140d2903e0281076680c0e40300704007c08840880c4c0740340c04116071012f4014050040c02080400480000005075681700383c404600181141e90140143e0080000c880002e42081c240700412041c8460b01c1804003041c1c1034020790341c03009880c403c202c540380d20501800e190f2200285409100c0c4030b88070004002c4554042c10005522 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 917394937 1250 917393687 917393689
    0x9010f031404060506030f2814070603091a070f11030c0f031321060e07051e040c030b01020d08130218070f030612060c03092009090c060304030804050c 67
    0x71910440d030640b005501c820501c101801d04010040f1120b01a001810540b5121843c0040001140d0b03c0c8800d02c2814a1a003000d00410b084100d840c001000304981c0c40c140d9407040038001c1d1400c0a000d90320701c04242c0c0b000402c200c034865030510842d00c0d40e03600403404983c1c502c181c0b20521040c030300400a102c1800302400c0000700300020703c101d0196400458a50303180d0800c81c000e664a40c0c00c042c18030144c01100900c04000042081e00c859800742c004528582040020351a12220340d024a5100c4606032a00c590403160f40b00c0d2621140d82950103014900d020f02d403d4050319a40309566006a1005000705825441400703807580110b01c4040c0c010424500b60002945104d0384100c40345900f000005110f40c0d2034200f141072a80d00d0050500b84115840e2074642ca589090000d805840a0348404000c035840d44130780c0c00420040ea000b0500103046041920700c900083c8810b540a000308804070101d160b0210000700b070144c0880c0144128a1a83c0d00c1c2c2e0202c5130400050001c440503c82c1001045807 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 917396187 1250 917394937 917394971
    0x204030b0c1b07080a11062d1324020a02100c0503040503120a08182a09070e18100b070c0e25050306030601030b0c040504060e070201050f0c09010f03 66
    0x140702410017485881d4003400c11040018080e0700781c6114203000c104400503421240010740c0c2400045d15039040e00b161149005095100d5440c1415200796050004a40c1040800003081124400c98100901c100040d0041e0390310174041c480a075003d4030703401d0880d2003940304d100b41980c450b10402c142d0381026aa04007103454100004448102080081818804c071640610500d510170030b0400c408151011118600d0345440940c1032030060003403804440c110040024951124100303000d808440e4034580113000030000312890312031610818299403445131480c0000709031801103a4210342518030500e00107a10065502400c2c01316031100c0041d00014680340c10419461045550350000d034201c0c0b4004111240e09801d07040400180070050060240e19200007171018103582d400180c141c400e031a0760116100314051688490380c4541401008180d0710181806180202061b80081c0015210407803075100e00c840031106c150b01040103006640c010362180b031100103584200d02f000035400c0c1425005c009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 917397437 1250 917396187 917396189
    0x8150a020d020f1306080603120f071103160f090b060913110d0b090a0c02030304120e06071a070516060c03060b0d02030405072c15031510090204030b0c1b07 69
    0x48800404c078820864107801001855024008501800c22014059081401c900890284882410011401004000d0505041000306400a0865a44407601d4030341e0f0302008c1942c022081001081d07100001c1c190564011518601c5e002842503007810416402d01400e0800c10f20380c1100780d81c03198424001200b05c14000c081c013494940d4007080741042c000a11404202c058440d59103079203000c2d105100958044281e80c0c1080c1e002142a1880800b030108903052840f219074184d02841c005291401c100c0c1560700d4840c0814020508145540c0f40141902c060007400b040d02d60300d10740c15864000043c0c080d0701c10040314142d81000115035448080090613900b01800b0410155400002e100030b019080040400900c4102d44550360f404500708215200700218240c0710125610300045000d55812134184951581c0c050100c0b200c0d0114642032440051080c5e0300c0c9100c4444e05140400c1d1a401f900849096a07000405c052507910b8551143c102c070f510080004c10543c446076080d4045c0b05050000340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 917398687 1250 917397437 917397457
    0x30a0c020f03090a060503190c0f02010c05040311131b020a0c0503070e0106080a020c0601090608010506040b011b02061c050601090b040f061b020d0311011505090a09020613120c08150a020d020f 85
    0x10a003076070110ae0203421100c0d280e000d6400e0180034801040082d01c07950005007844001e80d0602194405904210042c0880b4080341c3e070b6000401099000842e030010710520a20700802041000d542d88805041d00c0f00c4250089800440207100113108044c000c01d1940d4014181e80750040c5030503411001181081001c0e0030510050b0b890704820840100c09028031030b041703801181d00700190405000042c0c0080841190003401c040041c0c0903006542d40d4005540c40368182003402105030002003038a070000c2104982c002e021a404070004207541c4014015103040d0f0700700200c0c01c07180b1428800240c5060000c0a881400e001d4000005001a280e01800400013842074072080c0c0307103501d8005003d081d00d03010003403101c5038902c3d1141000309030b0350030143c6600140110000561181d00c0d0000c44d44520401c1d040501ca858a8680003030841070015500380164024012040120348846955484600e008448541089200c0109203400e0030380d8010620001e103480014684850036600e00c0258010010740 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 917399937 1250 917398687 917398697
    0x51c050a080a081806061905090a051e071407020f100f02010b062802011404050c01031a0306061009080703080418110403030503100308030a0c020f03090a060503190c 73
    0x142040b00c0e00920b4658014126140113044050300300002030b0b40d19030090525100e01003a20170885800103072103010700039140160504c0354600c0e010f010000505426200c2e2101c07485800c58003481111124035590099207030781d65880704001c45400e0801250040b08090ba40042803000103280c55079041c1d620305005020343c690b00c4280104000103401c442940c0880c4e40030b020108900f210034421001055a40600501d124501d00303000401240185245200034254105440c1400107000b000600e041440d903090341d0500402c0540700d0030310b01d0070381400341036900b5502c600c0201d0303141d140c1080303230784070b507000f246445021665030300516407400c42e16030f000381c1c0c0f004e5000900348000103c034107003020030704141c05040c02405c9580748041950b100d10310020341000008004105001141480e0000454100c0b407072030340f64109550000010000c010000000d44943d0041c40001e600c04401e03501c05140003000c0204aa00d050000c0d91b00390b00007849000316a000d6101500142e07414480c00c01d40a10a03590 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 917401187 1250 917399937 917399947
    0xf0a0309020f0406050d1401020c03071a07030603080306040903170c040f0f15050f09310e0319020f1c020d090f14042a09051504051c050a08 62
    0x40c004407602e800d0416001d181803000130f012139200e00c0c022102d0143d00c00c40c440c881d906103001450090240400d4440c25010010301041440781c00561909200c031070840b485201e844400c0b0940c22610a0300c0024a1130105000007512844d040e8884012280a811716444842c10005a090340c408116840001d0309800324043c401c0c45540125103014080000703420f9501c500304203103031441c0d01d480d842c072500700f0400145418140510030700b81c50790002c0c0a40007100c2003149079543c2d000a10219804240c9500c90700401300c021a150080ea030505580b4400765107010352106205419941091006040d48035000074203003880d200300440900e910f100710034070380300207120311000382001e0358405008100300440c00d040c40100c000c3c07840041181d1580c00c2500b42001103c0c0414090302043c0d0b17a842e2381c0280741c4110a000d9408138100005c480623940d0310a03e039074881007001080150181c00402c03600c13040c04280118148200800c223207200c40301803040c0040e50341d0369241c54030f40740c6c0b2800ca5519a011030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 917402437 1250 917401187 917401189
    0x306061404090b0604090f05030d0603060b010305100504110f0c1006151220130512010612020d02010c0203030c0706080a0603030c11061e0c0c01030507140904020f0a030902 76
    0x4080c036100442100c003400451241c0e10382401290000c1c1c140d034421503954000a04000d001c0301c04001c8903511400f40d03900e071108045444000c05051000340e40060170400841c18039882440341a1144d905049046985410502400014108404001e010450800814041c2c403c142c010700740580428009141a52a05604800b92040750307010450001c0c285840081c001d800101c8200d400500145c00079844102c014038070060701014401003039101c80007503052090f200060a0f00265042504c818001c40b01041d056803c0316940d01c26400c540d021052118010715100000318105130051400b000308585980001e820740d80140c40d5003910707902030402004619041020264045504c90f001c00c041d5140d503d0240080c50b0198008060051100743e00144c0e40d00c0d4026103651410f0000f0f1703008010302c01c5008088507440f28046110b2486040f140303254661107400b0b218818005641d03500504010040306550903004000c6a5501c2602401810200c40c456005040300d050150381c0401d416000340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 917403687 1250 917402437 917402459
    0x120318081305030a08031f0512210306010f03021b2e02090a032306070f02070e01080c0d05030c0a080703030f060305030901110307020d08190305011a0919030606 71
    0xd07108500079040130082d1808540400c0c2031302d61100300120305120044841c0070103d0300402640129034402e85c10104604810000074490451040a21134595002642000d26246001c212085400114160500011144a6009418803428221414020b512208611403d040c1d4a01300003008000c0808450b0030141b4091445001d0444100214500381042010464512170b60102922800101909041002680034a240407016400c20b8940c01d0505420040c62041540c03640c500520586202054800c259500350b4101c1e03400c600188550306030407060211000d030b180c0e4152480e001c02d0140100000040c8403510000d0f01c034500540d500c0c1c00e507241c0078080312400708242d402145410780500000b90b000007104c824401c24248040c0d4040c0003118145107115800c0c000350846075071212582084131450280480341c055400c02d01203041d00e10b40c12002c0795002d218008080607284581c0d06031002070002042c419101810840f1000720355040380c481c1804a070720072903a8680e504401c1008806030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 917404937 1250 917403687 917403689
    0xc050607030c0212090d0803130606091505061303030e0112020315010f1809021303060f050a05180703110117270a170c1905010e010605010306050d1203180813 70
    0x1030703039a00c5d09040301c66000c510003216007000280a40400404543c1e00c860700c5080005a95006905102668a400c0c0180250004a501c2800a6900100840c1074030380348040c2d940040c1150b80700540e8034130b11b843c102c0340070b00c05165281c18000c0c400c4004108e1400ca000a5101d43c0d00c1c102c2c802d001c800444001001c03841c3e0510b29404020401c804590401032404189040740d5103a036016807128100c541c01c11920110384c2c40100301a02c2e01d03e010b12440900e8100b1441381d007035214108555030741c85001405401d090020300c500b9400c00769042c80024032074620981c24080624016001d034010088098080106407858040709242210b450003030b4003003d00b0701c016001d108029108208440e50380c1250032000444100342400c0c081008068400d0400503e50990b440716100300e02000d20f420140d000300410a400c0340b90b03508049020810b54040e0280748100c0388082e20b000c0700c02d4140d03107440300c4060a110010302010f0302d61400060511000040050441c082e4503a541e0710f0b5042c5843c04070840d0a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 917406187 1250 917404937 917404963
    0x606210309060e090f09010b061227120a0e0901030321060f06030905030d11030708060d1104020a0c0209010b0c1510060507052e140412030c0c050607030c02 69
    0x1101c0f10110079446901119401c5448040020b069445030100daa000d41035180407203800030004a00da80c1c0b03204103c1400b6000c0c100b002001c040000420410340b060030401d90004025502003480c0340b0282510400421070500586040e40701801800002121048280e1090300082c0d00021040842600403109200c800001e0000308031680c50855201c50640e110701c81d03e01415559041801882001d004540020700c001d042082040a2a005071b151600103032040f80000d0620390009541c0c0c20218031240c4520f4009082440841d8800c08010295000d0b007588410440c80386404d00058840407111406040180d54107034442e502c001c0c4003031620452003079801c018552502440104203002c1d01c07500940da8145070042e661601410308928000504c030306906020040300c06078444c41212103812500d03006036030051101d0000c007a20004802805d403030192840c09441007a080c1603001341d0200f0f02d0b180260906a80b2000c40d502c40b182003890881e0400b0110391941401d80410b42c1c1409410301e1820 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 917407437 1250 917406187 917406197
    0xf0215010909061805060a1a0306070206011a07022d120715020102040e040b04020a08030d1b0314070318050f0609010501060906090303081009050a0b010e04020f03040609060621030906 81
    0x840b603d403e0340d1100041c1402c4d080607a14450300d0292813804008656400e0049c040b00c00c0340c102084000d54585003482011805141c2e4408401940400400c448000340c0040c48142000104e0b40300500b03070314420004600d60380c1079841e030140d03503142d07500340f003102004100c060402030b480e02a034010700c8a280030f200c04c00c41e4810801441400000b244042d00540c000e445801281c0c0c80380b010070004440f03500315000511022941c03a010300c001d07402010504c0752840d003143d644090303000d007a001e9680d40183c0e4200800c8480010740071921030f510000340319186200078060101d0541707440f814800d81d2052405150040010030051450074007034580100041e14042d54035600e8a0b50041040c86039010040402044001181200a16403685800380100460820031418256219002011008035450114a0340e03000c180340c1d803410b40309481d89590102c1d49149142c0c1d42d655283c009245519044408540c2c0b120081800001181c5100b00566211210001c8820303505015145c00e00b50b030b00100401c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 917408687 1250 917407437 917407481
    0x9030309111207211a0103020f0406141909090c050f0a0510050307050d0e0307050f0c010e1c05120d0605041a040518030a180e040f030f021501090906 66
    0x820b00165481c111503c2c20072208112800282001940b042e4035405002c40070707845100402c4c3e0141440650403688201c80800301300704103409010039a00c487c81280351718000701c1d100094500f0442800082c914000340340b06420b60300e41c01814101e40e00700320152140c07a031440e41400f02e4140b170721542c1d11400e0100c803944d48451619000800410000c40d03203a080140c08800f040c0028010400c3e200111240542400344c480b00d20306c900e07075a4006600a49680c4162107050f4000a401308124080f10010303501c103002808104140801025082420480b000c0c100420700c010072014000508105546080c2a80d60281c0c66000b40030303200542c21044c03040d403800141c130403510000c4003210380b03145081e18003040a03510030308161101c40c94010102694000042c3c07011645501100b030310818a88800d1207070003552291104039029000b210014180801c1d9030542011900031050403040c0c0f0034034812140c01030301000a03146a002c003a4014a041c0d62243d035081d0401500b8060420783c00142d000f07aa11003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 917409937 1250 917408687 917408719
    0x303080411120d1211070210110a030e0102300906040314010606020d02120d090503120c034014030703020a02040c05090f10030b36040312020a0e03010903030911 71
    0x621940b58020300c5812326040d01c030340d068002e508401091015100340e45142501c0c0c140641401c2940e2111070050080b028261081403032030031110080c0200c0c0708461000c14032421142e0059009211a0380d0100b0180400800940d500c0c10066960391800700102d80c040c03408034080d10b00502c090010b0150340003480c243e005074051105031500a400c00d00081200740307041c203009045119007206078140301801d10400c084110b4501c002d600a00c400700000c842c0d40001d0b8465000034000e0f41c1d0300c50052002c001c0320880540d038449040c120b14003c071806e01d0070441d02c82280746551b0040604601581215070a00e0540c94988a142144131a034280342c0c2c904070004000a40c0b800d0f5449459205210f4043d0580a0510990060f0800000500642c42c200c5a400940c103a400d20007501007001054143c110307881c1086501e13030754055036041d224810f03c940b8943d2400083d401c11120542007100440e0805c20b203942c00d007c1c400165000c1e0310001849501d9040c500e40d1030080400c4075010f15031800c81c41040d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 917411187 1250 917409937 917409971
    0x112080f0304150f050601140720061b250b0a0c0618081c060302060711041e1506050405150c0c060301150809160303080411120d12 58
    0x80c5084140c8065560b03511403419020205109010403011460050700c120f00e0426603104034003d50090300d5803080000400d03054119403044000c002c05948074003801c041c00038401b1802c48c286d003800401e42814150001104011003c501d54450400d60255003402214036150307540300000c0e58001e00c001031145c01c201001c4a203103d1120b01c1d60030030004000500a003c490340c8041c2d0402c0c5142151142d5500e1ba0504075140d400546a6101940441c80f840c02110070707502c226411640d01404807800e0201c0381d02d65400d010601c03902c00340c0290720340c1040b14400224081404692546901c00201c008548014640500a54000702d0900c03034200710501c2030b0781d65020701d000c000c0e481890240c1e80c1e40c0349001c0f481c20325001d181c986030021000310006c1403c06800c41050b081768581d03070b1210255910412866602c03000030a001c0b000e803206240500100e0b1007030004a9205000705034110f48001c00380e0110300b07030b10b504500c030a0304d54119601040569030300441e52070707903250700035001e01c00d480c410344e03030451 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 917412437 1250 917411187 917411197
    0x60f030803040201031b0302090411030f0c070507083f1605010b0a031103161d1815090d090503060f1b16151401060e12061e011208 58
    0x4000001c03000408580c03080c0c100c225040e40104505200740e40407000a1301a4100c02101c912030b5042400d400f040c90000c0c005d5900c5203400c481000681c2d150403161520035440352400740d4160003003130700203c0c0c24131307003088500300d0408140d1420750908900c0009100f014000e0404d90309005110b5520490383d002902511100c030324650b45440941d5140c03030145c2c0103080300320126401c00e4074078000006005852a401407500f000b50b064070448440c2c11032032402d00071680180b80104085203108050b4010582c00036601c13240b802e42c03130903542108881c40752034082076429201c0b19154800030817040440501151010489030f041051000f82410b000986a605c010a1501100c14250006050380c0c403195030f020301e126842002940d20385a203048450482c403500025100c0312500603100380203409a00c0384020006990f02c0001490b401c248007107903840308031400c06502101203034a2048042e17041c031005014142002d02901c040803202c402108518050740b0440c40040d00e02440408174040d042250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 917413687 1250 917412437 917412443
    0xe01050904051b01030b1801090606020613080901031e0912050f1c060e09011a10120f0f060f0305060703051905091905060f10081002091503090307030e04060f03 71
    0x1481e80f000d040101c00901c8441c111a070300c00348002e411403140f603030710615a042e03420403281400955240c100c140c1c1c1d1880e003510100c100e107180d440c81902240c0000080d000c200c005240114040c61540000b0055015221001081a650706514030800062500c09c26600c503007401c1c00c0b0f05120603004407188078001d1690f0040ba00b02840c10f00942d083c4154001006040c040f8650122810f103c00b0450080c0b5804130a070382d6100050b8403036100ca1420b035101c0c801a80c0030341d07194400f84459907071120184c4602c00800c0d402c19150f819400450314036018040103406160090441d00c0d00e9030a1030b500e04000034005006151818082c0003460365000f5442d41501c204200228a81d00c800c0760580c034040c0c000c01c01400e0241c00340e03007107010480041070050103011503610581e0b1684828039904503c031024480c003e92580140c0c054041d511103900034002c0c0d004024121403000002d030380c160480383c1c812552605a50000600c0c1030406411280000e035000041c3c0b0204085800e00940807180ca80031700001e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 917414937 1250 917413687 917413723
    0x6050604180f05190501080a020f0d061b020a020103050c0a08060d1403070b01050f030706121e06030507030302060711101e141008280320070e0105090405 68
    0x146210001900b08000c00d9150120030011440d10344900030302c0d010103400d0000c9042c1001c000041c129800141c0c80c1d5280e030018070505c05a88654100141400e40000c111142a00d44994600340e0318540890288080310f40c025140ca030741c6a10004040751402040c03084c3d042c60500015110560280e24a5404001a200b101c051900c2d0305001c1c04284580c0100c402c0740c403000070303144d00b005182c810f00d50494000340c41005c804000781c4205901d403c100e0250700d0004240c040d19409140e00783c1c001d801078040ea800c4100480d01145001410313151650802d0390b8561044108104040d810440540e0050381071405850300380b0136145480d110b41603420202030f8a604c40a00019194131403000200800e6110801c0152400000004040d10b100b200c0703440c1c600d41614400251044c02003000011660354040e100e044801114050000290350f24060f42000b0000015145841d010248404d4600c4444010300d1000d00d48400400380038016003151f8020308049003408001040050321a480070040c4401c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 917416187 1250 917414937 917414969
    0x114011802160b04300c12031107060507020606060c0a0f02131508100b01090e090c0904110301050612030316030e01020a03060e07110d0c080f0a050306040f06050604 73
    0x88550314140c12000b41080034035100f8882004401d000141540c095007100011000352960a548142d440f441510041030f41e030406d80d4001110451803412074030035070800044203000200d600d540d540120008848059581c003e00400d80d03010800f1b0765018004965842ca00fa000314001610f581d0354400082074055402440740443d0303030302c4060000c0b01140710701c01c00408002c4030340d027140d00700c2c5407040c00942d0045a01e040a1040c160144855103401a11400d215a01c5c3c01942411990010103080303641c054a41b065900b41d9880d61168003550140711346810001c03404d41014211030b07001d00301030312a4400e420b010006a1021042c1e90b4001351010b408040040e14590a80c0a0501940713400c43c0f075480022400c0c3c1d0b082c0c05038085010b40d000100c000e220313641d480b0f07000e031154134500d203103055264014074407031403000d201d40c80000ca0140316014823030030081d50300031a54980c2c0013001c2020110b10b0110130403007503041a11034030004800310704040c000e040c6407001241182c0b00c0c81c09660444c40840f20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 917417437 1250 917416187 917416207
    0xe130e010911041e0c2001091104060f120c0302060f030103060605090417030709080f0d1701050a0b0f190804031715100c0b040b100e07050a0806041d0d020114011802 73
    0x1900b41209003c031341104c246d410340e0152990003019034200850310442c09201241a6080c28071854040c0c0e40d6451f4a030300020b09004843c18403090450003145e80078149480800141c903010b000d40401201e8000054503541180f90240c20380303100c0e402c518015210300c005c000c0800d804452039032201148541d0103a403610368000407140e0040c02e41110010b4820001702e0301c013050303000411002e81c075015a1080f14014a8202d4240105000e03c80c05500c41c1d5503060901100018200030311500481c050300703a02d082c3c0d845100003440415500c07260b021440c82001c2100b45508102c0ca601100d46124020900d071601c1c1d0159152551104000d0b4084c10181007504400e5024114001c0100d0f040000d80350b05207001d140c011000103040750f1803d04801c0300400011540d1b050075032240101c299403201800c0c401101c404075001c5500420081d4407a8840314005110003902126550032403000002e0403d41c0d100210180c25190151100318110841d6001000b02e280003401c1002c4d844d40303075400942d540c0d41180c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 917418687 1250 917417437 917417447
    0xc030405010e1e01060608040c03031b06060306051618030b100302030604350403020f0f180a150e060d0609080301080c011704020d030e130e010911041e0c 68
    0x204200a03d2140c203089604080024441c1d10588503414020311a1030b468100c100c030007038400c0d2401030842020080500c0080d010709444c140000050481620445107a10350006440003944251a001e0b0340314184000704007100b19801020500341000315411005114410200c09684005040d6901c1d030740115024400c1c1c10020030007141c00a00300c403154242410500142528224082c21028260b429035040040103289100600c1040c0103841c10685180c080c0403401c440802d1090344030140002c443c8460340d0384007a0b40002190202a00c01600e442080d4030100c484c0401c4a0700b084050080400c403000302201455400542a908075481490380d2900c10058502e00324010221400800041103001c00003800c2c01d04100240d070741d90840696070314142034102e800c1d01e000e134101c0030010050002c00d0241403c0d444104c0b0140c4004140f604c003000e03900455000402030380050351603108a0382403210b0364a800c03503240003c9404101751103005542c5442e0701c0805100c036141c0340d1288d00c4820098068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 917419937 1250 917418687 917418701
    0xa020a20010204121a0f0115030f0f0603065c04030516090515040b030c0310140c03060f0d0602040504050f2a0906130b0f03010f080a02090c03040501 66
    0x7581074a152900343e41743c81082d00c580000080304011420300000c80a03c54040741604880c08000b04214042c0e110004402070320040d43c80450003601e030040200c21909511074100158040c000004014956501c0d10f0140241808641c5524001c140b280c040082540720000c02c101107050070900b60004000000300c481d80014403c802184089000003c0c800c0100d0650b0384181514104811144c4801c0050b0403a241922148180d00100b804844141025444a07440300c00040445194000b03aa0000340703441c0c455118203580710b840d50a041340b902e904001d0b03d80c11509003003880b415860701102186049040e00e1200d481004030a4529050244c150b0440c1c1c007602c0c0c0a8811f0003240340298445007050426182c2c0e0702001d00300c10303040b60100704501079564a2602c004040f8904103404003006050741201103281c5000c01ca00100040645401004000080401550700d45a40c07420003140f101c8035459000307407155003040303d00c2e000613594502c5065110643e100980c0d00c0341c50300e0030300500500d22 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 917421187 1250 917419937 917419949
    0x1c030b0d050a12050f0901032301090614030a020f09071b0305030403200705060c010e1e070f0f1211100e2718120319050a020a20010204 60
    0x215600380000d001c00801d0a805060148940468030b442c508011203241c41003162080364114148002c01c1a98401e402c41c0c0843d02482503284070000d158250864034820a03844507104c550340715820014040300040d290100d10045014151a000c00c0d000300d645034081d1502c841c170440c1e203080054590790080540c0c07034440c0800c003200d030320710005071070040c10540c02554140e010400000c40e090800002c0005280c90801c0d0101905001e403070402404056080380207000165529410352010200d410428010342854040542e8441c1e401641580d003060b03203d820021001c01b4006040c0810203103100c0701070460384a0075081c150309419080010b114400c040e0603540c82082441340d04011544003d0011b44520101c8955140e0044041c0c0000840082c51488039511784043c00228245490a0501180c4d4040c0c0107903030344813070100c0e000b203070710340c001c0303c4414000c6005040003851801c0c0e40308403580049800c10031803401e1000d120140c4840031201412443d02000d4590080c1590207405881c01062 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 917422437 1250 917421187 917421199
    0x7080a02011d03090906041803081918230d0e1809010c081006020a0305030a0612030203070506070e1302070c08030f041805011d0901111b0c03010606021c030b 70
    0x1001400291250304c0182424407503410742010802d03900c0c2522510000b5142c10420441d0000559130560ba012001000d811115400c90a80d001402c1d035402507103480d042100c05403001c0419460030340b6404c500d00e01203003c0c0389d0301214003204e140e9001078101c800043d281030034200008803400080c104080c0c076003501c560f40400740c01e00c140f0b290150071011888003142c030380b0222030b940c1e0200e041c4051510720803040141e2186491a000c03e0003400210f80041c2c800c41d01081141e00c41f45540140100300d2411001a407000480c481030140501c042a0055542c0c5003070129012006c1c0010058501c0c8108042442e40c000344200411107095282c0005007400c034166600c40c9913000c500d403d550010311412882c0954042e1f00714000f405803203400d042ea80ca401007401045606120700e400c40f8001440001c01c0c0d940e504010300342e554508090048884000001d541c0e40c1c0611000a00303200b012000c141c044e03814108288806a00416900c000d6461200303443c42030080701008130050201c202d50b49030401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 917423687 1250 917422437 917422481
    0x302070515130f0611341a040302031b0f0f010302130612060e060a0b070c090f0522120f021005130201030c0c110607020604240e01050403030507080a0201 68
    0xc2c03190110241140e200351a0b45444c0d02c1095022511440e1401c11131080741200101010405500e45d44002c088410980960340241c032445e1440001c000e50700c0c0c4081820300408c040046140c20400d65022040c810010018040c100000c60307000480124400e201700781c040c04140c003603403096040c0c4050302c0403000500c02c01503840350081d0003540146040d122546c2032080200b145000d2610841c000c0d10040c1480d4412443c1110140582d0480c160440744c644400d100080c0d0309a0071f000d0b0442c02101c3c010f001a103030408181b804900044048100c0140c054920720f840414140e20007405400030b141000c11000107400b03802c034140010340750f000407464038000601600d200d4900210340d0540c400c0c1c034208540383e510107003503d0044404000078107010700c0445048541c105100a442c6170792001e42118142a100c9051316071440b4650140c80ba100c20000c4405042d50740302d0789840d1003100031308103a441c1c01d003561402401441101001390112000090058925200b540000c00009001642c52040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 917424937 1250 917423687 917423699
    0x8091c06050f01060807020f030316020312010e01140a080c040911030f030712030e0607031e050711010b0a12060e0a0c03050a060e160311030703150b0a080a030207051513 75
    0x2c09001e00441001440c4c2100058410380000360801141030b0f41801541503903150102ca228900d0010340c1c000450000744001c004401c1c0182d6000d0281c000b01d200120390358103107100007107074801a495542c480c580e84003080020080100c0d4050496605450205003c80d441c00c0000001e11108442038140c8103465001e60801004000f50092600c14131502c42c0700070035601e04405441030864119566005140404d60310790081d03000916a1800ca00211400480c42c0d07003240032034608555a20110b0f5070000140c2424000f88980c9066006c21104680da10b81404840766080380a04001054540e440509107240c103010071145211742c1d4020b03410f4034107907142e103061600c610341400b00311126400c00703140340c81402000c030348006541c00c5418114491455512003031419030203141e035241c050180d001c2c040b010512a041140120a104802143c0000e800061148104040d4440c01c0307140c1102500600090b80411108125030088560306d4002c1201025503610f07205401824950241410002980c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 917426187 1250 917424937 917424961
    0x10c210e0913020a1503090b0f01051311030601050f0909090a0b070e0f04110c0615122103040312020304050d0e03030a210609110408071208091c0605 66
    0x140d80c42507a03641c500762100788030b0220700280300000030342c80030a0050074001e41e0110040500e2182d064500410701c01c80343d4072000d403110305c1030755074251190000d401801035003080c40120a009200c14020012458100b0217002c0e2804060003150400c80000307006440d2840e01c809407808004002e19541c2e0703504050150700c1d42c07800c4000c07007144c1041c0380100151445006400c041c102100192003400590101002c00c00200929880c103c2c0050040c41010481042001554450038180e402842d86c40b07122420403121005040c3c0300821940b01a1580d241c4180301d01c1640c103d203a181d003000d078413034a6a249c1a9014030b07101001c1c10002d4070110401c024400001010b045040702612009a94842c001c285903c0348910f1003c0c1c408070300c0b80b51203c80f2070326103d4000312a80d24106000110f0580356414030094a08124102c81d450b000071906101c00d902c00d0044100034800305802611251055448410714060842c0e114411110036007503014103d140c032440c8840580c0104100140d04e8001c0038500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 917427437 1250 917426187 917426207
    0x5070507090c08060915010c020619170c0f0f090105120c070605070f020a14014502010f03090804050d0b0702010606020102250816050d110102070b010302010c21 71
    0x5810f40303000c1841e80c200140054003611505d590890031b10203140040d1086d5004100490700f19400700100c1241d03414002168003040d801c0e958032001e80304006408405c200c400360000e0707580c0c0030401c500625035522001f00c950715034138090b1540d126040700c00140d03014003610781e41208640100c010850f079032842100404289201e007404104c643c582c00c0b02103403944a10361128000d0ba000200b4030000c1000c005040320700400c1034001041c1030b55100d0304405851348207100313441c01d806c40400341400c4000d002040003016400c1001042c400003240c00080c0345d401902e041c80145540c1314400e0301809440c0c41124090200900200100e042915000701c0b22602100c80740b00652030403002003240342c418001c9a401c604034450010b0a0000d00165126a5211000441b0000c0b410001800150080000450002d000302c001d8103070074102c960081d02d80074604612404592040240100140014001c903040d00d40a1038240540c8050385025801c41280b03080340c800404890454040e000da21905a00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 917428687 1250 917427437 917427461
    0x12080f16030f08060105030c0313020a080c0f03060609040209040311031801080703140a0b03100c0c0308010f0617060d060e03220302030c091f030f030801080d1e0507050709 76
    0x2c5000c01c0e0301c0c08898101c4140e80c01d6000031006c00206194000050245400c401d0381c480c16802061142d0000e80408007030350080ca03054000740c80c0c0c2481450006004401000240c0203844a403a210f000103012880043c0024410004400410241031240089034142003410b81200c2e50744144010840ca407841d134048060004c0d9101000442071840b81c0583c400c683c10011101c0b00301e849810140000d041c0132440c0d650144a4904240c0904410780215404c114440e1144000420300b403c0081c041a0140c00c9001103000c00744041181c6030780107100a28280900c031040c1516192200054420000b917440a0a6603041501a800411011009042140c01d20301402c02c0e916030030f044610700842c580f0010354140c10000c0c5841e000e04140700d1803903007c00000e0008594024807018881d01c02d480d50815103040408050103810903400044060142c40054010698140000030060038000c070822050a110142d441c04000c00d030103a41601c10055101003070f02d003102e4880358041c3c010400c1410f44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 917429937 1250 917428687 917428697
    0x20a05011e0c030213030201050c01020906030a06050306010503121c06030b07081501030e0a0b100506030a230408033103030b0301051003080a051806070506070216060912080f1603 79
    0x25001e00a10855882c4c82e0311817680c8003200c3c9150010749142e00300380390380103041d5000c0010b400305603500c50085118070345801000410342e00780380c1030600d00030051700a18082e0340070340c0200254240700c80a542e07005120030104541c1d0b0b80007000840141c0b210754401441041c10800b070080d002d8100400920442c112004a0300e0307007202d00c004405940300c5003000496508020b62090201ea420880c850388241086090600301d075440000c98001d600c100e80c03d0489540d02c00583c5e0741e1075080c0c0400f511551b0621090801c5007000d488001840c80301805001140080d041502859490f0003080803401c05c2410345041802e07140d040180103801c035429800c1c4a54a0400090002440d0083c100180d036003161a107070030003094160a41d8140c4c006d5030050365030498034104103040c0c0d0700d4000811040e44a40050070203410310540184c50f01c1c5582c08500c10f6000d01e40024402690b01809c26011180841c0c6039400301121400e01c0740b6948922060305500c1c0d50009400741e050400001c450700154440d6441d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 917431187 1250 917429937 917429951
    0x6180e0f0c0109060c110603040f0501060b07110f0103061802073f0905030106060507060c090510050a170901150f0b04061d0a0305010f0b060c030a030507020a05011e 73
    0x26039a00e612180300398038086420200c080c01a940304842c030f400311a102c0e00100d054540044c0004100b50421a01111400100b81e000c4003080400c2c00b90f2001420a064480d0800c2c44e2950f520300c1a482d04005640140400c011032000783e8440d40254008007a840011110304402d4110308001e9071190000740e602202c00200050303118444591100d100790400414165804041c210404284030103089108010941c0004100c0395801c2c460b940c01440300f45ca0325680c5080c1c5152800c207a07024051007005100352100100026116a00320711480b00c4680751241e682c140c041c4e000e42d1107078603800350306980360520f208003c0c0b085015071102052041b000c40440541d0b41e10f03c1c542c0740350700d854011000c80311400c1c00104552401921891040309206483c4074002c48004007158a2004560050390726a468010441d5034000c103100d10000b00f030055900d20301d48603110000564a11070081070303008060ba140000360792a1302c00d00a111860b50b1201c001c2c0500d50041510542c42c001d003c01040e485850240c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 917432437 1250 917431187 917431213
    0xf0209180d0203280c0503120709050f010f050307022503061803050711120a050601090606020a0b061e150c1e0d0f02030418021308120301031506180e 66
    0x419500030348294400111a200e401340c0700c000101e507a038000c005000d04810242c001038000c0c80034140030f0704466905101c52038a81300003800814140e210314050032030290b0001150341c0c00314200c00300c003200381001503507a00ea030035040b0315000710000c0c004030f08890004202890b03a401090201200c1c002c2805000015280340c00d44400e51603c00014003249003041074400098120340c40c0610440010070001c000500c0120032401c0c03c8414000f01c0b0f05400440040c403003c0c00b184900c2d80a800305100408400040c3ea0310140380c10406844903101d20080903200440e6503120f4180c07090600c009e07140c0c603e201d195400c0c030400744d040715903941d066014113040c03403046a800785042254580e041d0000c084211124030240c0c1c20750342d070441250071800200408200035000c51900305002c44800f10041e41d500c07280040148000c20354100030f05a0f0407846003120355095050030b9030305403900640c410083c1c0881002441c014421a030221881303042c3da44026050010381e51001030038400704400d449414203950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 917433687 1250 917432437 917432443
    0x603120301030605060105120f0a050702120d020f070f030801140d0c060e030f010509070f0f0614030a0207020a09050f060a06050a0e03070f0b031815060d0f0209180d02 74
    0x44852040c0300400226440d0740210b074000c40c040c1885450303c0707080c0e030300078030807800827a42c4003a003546a005101d0342c101207105031b0358003082a00c0989030318025820f41000904c01c0c0d0030403a1160360041160368880e00300d00c00b1242240e6200036803001c400c0b07144c42c4c05001d81074244100141c080c01c08000a00506210041c80300c121b40c8201038000c12410000169112a00609881e4142c81a0110320175491800d1040d5405941c1e0840100f070342e140780c601d03801c1032150250020b809031514054104107941d00040a59043e1009900c02c41c1c0b00c3d5250f801100090060070780203540f0600700c0e00001079603405d6500090051090079850341d1030703a40f040144201c4004074030842c0000380082020104240c45990741c81c038880d0004050b2103403199151100ba2413904107800a10b5405400414081129140890075a01d5039500d00a0701520f0410402543c01410040c103084c0148880003280c004c12040ba12090812039001b8181070701c1d42840d01104203050342500800d5a0303842001c6401e206c0c0c034000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 917434937 1250 917433687 917433703
    0xc06010617130312020904050a150506090a06270e072c01051b100608151e0c040806090f0d180909051f0207060510050d02090c0c030f0c01050603 64
    0x20b500ca03141550080d034044948813580c2c24080c0c0c00940c01e2244072103c0da0b5900815001e64000701003ca245d1208503000da14200082e07108611465040200210316120012400102e4950381451010089908070100c90509010081d9103010030213800030400e5940c02b0310b11805613a850b0b0310482d54800110380008000d52005d14046000000c00503d0101d600c01c030001c01c121500b880c1d80e8039506042a100c549414444002d86c0c00c00707921200d0074808154100803505041200240b44801c40c104a4200d074a0740c0705a19004003100b203450001520b1810503422900203100c40c108494036803400514898640141400d07032036050289805420302c0391310500f0406d901400e05d6008140c0c0130318200d40c8000406019001f12064041c3c2d140100c0c1101407180300c002003034507680015a45441b1b5141c01070464a00030311840114101c100c003440191290540b4100ca1503041e550190b1a40709e09104001c2070181407403601c0e5070300c000100281c44282e046c5c054090040c211000b480b190b254007013010b890f03501c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 917436187 1250 917434937 917434951
    0xe010b0a08040b07021e150a02041208091917160f090e0703021503041104050f0403030203040311010e10061d0403120204080d110d030b0f13060b0c06010617 69
    0x1007000c0340102c1c1c4402e0841d40c01a0403030048606104421040c400c144081b000412942d4221140d80d4080b000c51a03019944507068040443c5013604109100314520807907103020704265008200102140c4504505000340343c2c0d1300c0c12554001d692000700d4041d007040c1ea40150301398001d03c101741e4070405030031500307005841c00ea4801824041c28922000d004003040c1010010b01c0c03145950010152f107500050354084122000880d58a1400d8100a49038404080125005030315050411031909031204030950032130b505150140e50394556050460b0000e18218103814194039003041c0c0e0714410710004070005900084001030090b0b84c0d89454941c074500350207440200f112045000100041d109000600902c800300c40018107040c0c6440c60b4070320f170800b0120401301140384d0103d90740b140c22040004c0e040a002e5840c1c1400501074800125480c0400c01062501550100c00264240c1d4082e41101000e420318201503a01c1301050341690781d82c1d000a01c250b178080342c4062800e800000048605034403c182e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 917437437 1250 917436187 917436197
    0x9030503070e0102120a0201020c0610060c0b150a17010c05070f030e03070f12061b090501031503150c09060207210c091a040b011803201201060e010b0a 67
    0x40e8160741541c0c0e00b00201d031154114000e1440b007a6040360315070007401e510100c0b5400142c070b03006040e0b055450045c01030414580c1440a00c8204503542d80f1100010010368071440a00085e150040d038001d040400d61000341e44007041d0342c000300d03000712000144030740d202c0404024001a00070480a43c0c0300e1140c81409082c05800042d0040800d004000014001c1005002c480140b40d07248030318592820740d40c01250140c0744a40c115001c0c00024000d49404c0041d41c840c13041e4001d070615000d00210b50a100b8030b4145500c64100f0b0f00c550b880c14021030011908013031800b030023200240c10030340280031826005c40416241100840c0746480014a0000e40b14019803026a66160510a94105000c16800c9421204184020034149401d005203004181650340401c1c861100c0001c200c290b0b4102d4001504110b40002c00b40c11000b40c81d42c950701266004002c070704601000f0a510545454139603007603900321010445e4202d07801415808101101d0801900c1c140756621264845940d2042d4082140003503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 917438687 1250 917437437 917437441
    0x20c01030207260c0f0a030f031b031d07060c170c0613050c0a170706030209030a030e040b04091a062202131703121305120d02130909030e0409030503 66
    0x41040c020382e030401000c1c004050400d00c01c219805d2a00a004100b00040d4110140304000c05030000c0f081b001c100ea07d0304013030007404e4526018800030310445000d10b00705901e5018403280e039540c040a07114490030307150030380d0401511140060080c0d01005c8084440c421901080c200c1201100256002100003401400442c3c1701e040080781c2094600c982a1174a0240140c00b00c0c00760380f4441850300410b89c55a070703060400102d44138a410400c540d44080281401040501000d035030101e00b90500079410f061440040d00408003240007010901c007a5a080391600101d00300740526000110140b04c00410910415139444080c00000c0742500d100d02e101c49a01c15600403440c0b020340103441d258102d031101d0310410340c2c0c0309441c51680d0005404940641c000080081010011503181d40d030102c5101e80c4980c0b10102c42d900c9903a100da0561080014a41c0852120610001340d0100c1d01d44402951140800607118881c40c0c0c02840f84440440100c0c5030040300d903006080a0050740070558243d2992815a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 917439937 1250 917438687 917438723
    0x310061d0718090b190e0c0c07080d030e070f080303010b030402120709020a03140411010f120603080a03050906060114030a0905030d06030309080a0b0106030b04110c010c020c01030207 81
    0x321005040d00051041c650b424907101040101994000d10030158080f40c1115580140a44400c10341202d040c403d1500206002402203c1901034000c0084104199189600080c890070100300750490905070180c004181451541a00070301070021860701910b80d041d40c1d4243d2004001820301c24050750f030300140300400c01e0468103c041e40c0d1160000d0300040da2210302000040c1800d04c107811404207940d0109001c428039605114202c40c07003440000c00ea0650800391a13009100d01d0f80d03080345040100d00342551030140d1142c0c1072100c0d4607882d00d8051102e5074a9290440b180d4011000d00e200292811001130f02c83c07030001400c90b000d910184c40d80e10a46400008038182540002c11010000c1e0b212800c42c2d00141080004060401098400140190031850000c0c100d81c002da10001d803540c072210750302c001305030031708240c6044580302e003130004240519001040160072003008040b40d0500c041586900c4203c1900502d0084045a00340c4800401040043d4100d0086800c003030094400d298401c941 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 917441187 1250 917439937 917439989
    0x1b0602032107050708070f0c051009150513060221030c03160e0a0b0301170604081b01090c080604060b0a0f050609130e1b0f10030c1103030c09031006 66
    0x850000c0c54080c1c40c0a04c03030348a482c0700e680886421200c8040c032207003500c1403000d8034a84401070700d011641ca86a10010013130041c0b6544981c01b075400319050070082002c25601400498034204d49040003c80345130340c1c599000c2d440d40707500302d0b501300800084811140c01500b1442100d01c6058044003060860300c803002158800e0b0000000322052005d00d440501a5030754205054000f001c0d0480c0c5141d0b2981040500c4100012408002c0004d501c400c003488002054038094a4000020b01d980e081101c510003011405000e0520f005400c1018034540440e552a01181c540c0c132840c0528401d1061140820038400101505d1190719908114140b00344072502d05070000b801c1250008001d45042c0c6e0880400c501101d48450039090070360702846803012040c0352141800d540c10301c00c9031312078175511440000c1505135080c00411410543e0720031010207020301404451401c00341690803aa141d1401680c04541b503840b0651540c482d01c500e02c0210540b41650283d902514030003041d12032154030140088023 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 917442437 1250 917441187 917441191
    0x30f0c030f160225031a0c071e0b0c09030f1501090c11060106050915130902030405010212070201050a1a100f05190c020a120210110c0603041b06020321 67
    0x118000c290303180042c00c909204031390b03400c00b10940e48943e40c0e00e54640f52942d088400a0184901303504002c020960380e4090035142d085130400884920070036110039000551400c1c0c2c0e001405074010205100c40c5103a0a4041d250018081d01211752203074035a00459542c0d00c0c0f44000b006150241c00050250341841e4000381e40d680c555081a6207400b2445007682c1c00c0c40070076080140017034408540040589042c03400090114241c440d8641703010700b40b03c080174418045011f01c02c1e0b8290000089000c204095040701e1203180c0c0c0c142e041d109424105e00090180c50166900d420690030036804030b04074a0360075272200d01500c00400c540e01024260800342c80302d48051400406001e002e010701e1110380c0c1c100e446d40d00320745407550300d000c841d500b54810000715000b1900003080c041401e600c07507001a15950108042544c29080511615078014051840d242d900101c45410400100900c4100048546040c443c9892190001052a22018102d0b620302800303d91007041c0c1800d110300054544030340d08a507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 917443687 1250 917442437 917442481
    0x4050f041b030c0b0702090f071b11090a051906140d03090506070f03140c0c0f0f040e01021306030c020706030e07090219030f0e10050a0b09010b030f0c030f 69
    0x242601e40d5903202c150110300e255004240c0b42a00040c600c1c11413405400b903036030003921203000b07944900303185030000c002c5a21708000254541d8600c034404140715600103030701e00c55031006280c48610b250034482c0340c1c05030030107868111049a000c00283c8a040d0103018110a0301d080c070945560602e5507104100385601c42420980c10b110030b03202c000c00c1d00d40718603004150f03640c02155210b840003600e1070001d010030740b40144510205c1091019840c94400440d44a2540382c045443c1c40b002980180003070281a0590310403644031707180c511500089403041d000340042d0480d041d6002d0ba4142d450b6000d8050354801c0c0907660060300510000e1060b00d02a90109440d002e680045410080c0c49a0441c012a4884620810240500b1071445540c9034140210000c3c0414580280030034000c1c0b0a9581d9161074140300128aa910744d00001d50784a0194000c003541500180304034420350b910382c0700603040d600580f8142842114500001e07002403421045134010340c0416943d031290303628966a4142911048481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 917444937 1250 917443687 917443733
    0x20310050603130506070e01140717040815011d010b0a1e030b2814030c1806031612320d0e032b090f090b010e04050f04 53
    0x45155141c02001e03510990440d5003a000042c101c4c1803117442c1c20b00061400303003000407440010181381d0303011200750b000c80d801c0203005440c2c0c85a407518849030240e1103044101624081000074200c82c000800d514084180042031602c0d980381c031803019140c0c2c54404d40805100c4d40e500104821221080203292202440c030b80310706140d03421004020f15036400505280042d89901d1503541d14071306540103030000c21030010040304440341e08048400c10000c0f4070600b562114101c406000c0340c3c800307100c1030f106608004d000f00d541460394000da0150510a560550191180c5c001a160040381980c240c0300755030403852007201005041e03644d401c0210f211a00300d245044070411803c020003802610f007044a400344042d004103245c01d1002806480908100b40c07295218400d503c42c0e10541420300401c034000c5026450220f00198800d883c803104607402402e1780d9840540000300d00720b0540c030556408400741e0354a800d40c2000c10800013540c000f48c510409580c1c584010400090400600301c074080003405c43d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 917446043 1106 917444937 917444939
    0x5040506130c020f030f0d0c05030103050a0f03030207140c01032003011e0b030c0c061008030d090606051e0f01020d09031203020f03071806050c10020310 68
    0x200071046560701d401a004510910031040c0ea413102c80300f126680c05010400800f103038041e91803601d4640c5042045c00c0001e100f001140d0480b40c001008041c003244070f840e012400c07011450b044092613030030004400050402003003540981580700280080605140014040e40e10407a10540c0152400c031001401a28100550b07040da124809041016251607024212100d03603500194005c0c0703c04000c20100b81401001842c200702600142e410716203c2c3ca00c203200c5455680102c3c255504184544100304445500011070280a40e0010500964490101d5030041d0842000342c0740d5280c2c00d90320441810081021040c5030002c0c4003d00c0302c412001e40c000c050031a1404014604180f54028a0354075102c1e4040d0340350142c40750041c56490421110141046020110484c8042c1c8068000607400f4003d100b03940c601401c10014004180b4490750001c001d40c8010005402c0d0280c80c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 917266187 917446043 := by
  have h0 := BRFrame.cov_init 917266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 917266187 ≤ n) (h2 : n < 917446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
