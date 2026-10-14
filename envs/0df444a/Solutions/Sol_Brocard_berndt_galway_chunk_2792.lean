-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2792
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:45:08.585796+00:00
-- url     : https://prove2.me/submissions/8005f699-9c97-4afb-8873-d861ca062210

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 501978417 ≤ n < 502158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 501979667 1250 501978417 501978419
    0x403081b0106060906080c0a0522080a0c14100f1b0804090b10051c052205160e041509020d0c06020105041e20040b0a080c01020607020d080619 63
    0x9558210b60054102c0070001d010707090200561580542c1c0c0c01c0d0484481400c0a02d48510700070041e0051280060800199071891240d6800c11581500b410040541a06880c2c043c02103182031183c11100f80200454000801c10740e10741810188800286c03030020340c4410416203000d2800792240080c554106440705081c450f40400110708002030001440c070440003041548601040140044801e0300400402c007081c00300420350305500425030804088040c0004041c0c0b00c00d42080007400040242001c500d180450017000c001001039254000300107001904e9440b900c034400003000840c00d0b200134001104161420307030120610740c480d21005200030b000034001c604a55510300c1849035075100001607555101008140480d2091040c1c00c41c0e10510036015480702030356610702c1545192405181610704100141e1503403100c0d40f0400700079000074200c0304400d940319001c83d41d60141510950041c0122404900c420f0700002c0c095030840c4450b158411282e981ca814003030347d404c0d03404403c00403040182e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 501980917 1250 501979667 501979717
    0x8190216140a152c2a06031005010905040e1c0e0d0b0a06060309020303160204020f070b0124080117100f090c06050a020c0f0a03062d0b06040308 64
    0x55030751082c0041c048003041c0c21140000d03201904d0b040d1488107030400c9000d048412008004a110511958407540000610303000141810100e04012105500048004240002a0100040300f0112042646d4404c0c003a0b44403420301058460982d004071a81e84aa0034000080c2c0e40384814001510641c58121200004000014035283c010003066030055503070414010821002c1c041c500c050407550030184000c0c80e169022954034402c49014203a4041a2094841103581e290121040034040c07060064880a160a00c5071004900388600c0815060025650300020303000094090035a016403229012a07281040102100030381d21078202080c080c402c10091085082d1003030303d038001030302d500c00201100d942c60901005a20740e041001805000c0c00752060341e590005040d840c144003981c00b8112101111b010407143d26558000901d01800d000342a01218a20b18103801d1604032000c4102042c15403410401c00c481114a007030360003000400061003c6820480100310740c82a20041f404d031110100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 501982167 1250 501980917 501980933
    0xa05010903060e010e2a0303130905060a05030d0207091a06030105010815060d06080f070803041401140c2407020d0509130c0203041e080703020d1401060608190216140a 74
    0x3000c1840310700340c40d002c90303218580d0606d0700c98038204c150021843d1001c015000700c000d4180d40300b101c4040b0385940c0001c4140d12510507030401054050101e81d40d1265424000c4d4441540d4003c0841c001c0c42d1200c52112171205070035001805502501e21451642800c004544c200b0004000e02040e15094603240e00940f80c1200070100d4900d14100002c2d9217041c154800e0030848a07120f02d1000381d10003c020b000c515404800c840071140001d9050380526440c800580780b00200604130038030380d0001305180007030000100d9290051505001d041000005601280c0541c1e58280d4141c00140e200b28915044039000310014488404010414000c0c024981114400d4446040e003050060b00040360030040800000105101c40c5622080e03160008e040480e080c1d81da400b5840041d01c5941945007040a10501e2625852185400e0000b40201e540300c1c0700242c0440e00940d03400c1480041d0342140058920035100341d688400c4050f60394601302ca1251034211008101c00c160031428081c000310400015455 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 501983417 1250 501982167 501982183
    0x4050a030201030e2802090711060a05180303010b040f0501181203210911060724060806010902091008070c030804050106091a040b09070804030c1104050a0e010b0a05010903060e010e 80
    0x90505c400001407042c010200400352000d42030202c6850390710240603000c40c015600c044000e1000589580e01c1e812040c40e0441030792a441c0350b00002001045c0c192540d0b000f00295900144010300c0345603200011240016055402003860100030320a2080440d0008060b40d03440c028a84410b8203040e6500c010800d41480040d000d4440d961a02c0e00200044d842004188a00c21150b140c240096900c8800d01070450f211901c403c03940e0b01600c0150499581e1002e80603000c7d41c8200c40d01d5603104d60310707640203501c0402a24070548054070751740521481060031500c03841d5143e4901d10501d100d6070701501d8209004d08112401c1d52110f00c00b05481c070151040c00d007c0d44c2d040800001110070002400119002107210a000d410400c0401c01071039000039074641c100b40c2c9440c00002100140c104050320a010b102460340c01401e00c2e00b03000e070169494101c039450f03200e018000c105010404041048244403485a940450064481000420440d502c50740f94444a8800440c03003040c0500c4440c10201c078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 501984667 1250 501983417 501983473
    0x809070b0a0c1410050114150d0e010903020d1e14070201140a0302071511030c0c0102040905010e0a05090c010221070524010b070b13020301091a0115020304050a030201030e 76
    0x2404d038950749240c240601c0340100a90402c404201c9007100105401003540d003180000084000707500305100c442940001d00c1d04180030700801842ca894038009449a98041100f0005010f091040034420900002c460100c80e031621080030400004441c61003c0d00018000d03810f002084100100390b2000d0001880300195542c2c005984505600d08045400480d52a0813020f40c0342c018442a101900302c1220380207081003200a403140f6202d003d640c00381c8116080304030740301d0809000061644030100c00c0e40c0151040030080c00702d0350343c08060036075401a201c410b07401a8410100400000c015194600307034854140342031480c00c200394480500e001008500607140c0c000b400304144400da04404990b01401c440d02c4006d02c1c0c0f01264841e2000d841000d070031100c440010300c4071103045540950210820543c045506514014588401c400c1a48244920000c41004203d4000703964404030441c0c0607100020201c2000a04503001100204541d2040080c0b83c820703e061041c04074040390822105c151 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 501985917 1250 501984667 501984673
    0xd140d050a030e0c0d03050702060403050d05091f0c02010e0a0306140402011709031e04031212060503010917030a0216050d1803110907030204090908190809070b0a0c14 74
    0x1d84120700804891401d200c45400d50442c0e040f0505036039600400442031505883c1444e12041d050001849512450340010140d11540d070501058a030480090450500200c41711134000481d000710140303e282d00c2e40b5600018101140210056004848070300824a0180580e400a80c40b940c80e50304030765072030448807042ca110408020842da070082c40c3c0003100309035648645490400081096803030090010030654031084034110fa00d02030301c1c00107a5005540000c1d0310a84090710000c080c10041c000320b600784007a824a00301042c68181401040c803c03580c072412910080311380003000b140c9a00302402d07807040182c080142d0351f801d25050026480c3c8074010380c080c00b540d040d8200003a00f0009500c501250484600030300b00041040e0031504d0000c003000f0340f03c1c01016650004120024451500100d41c103500d080452014070407400040c2c010342c0520040510164030f443c07800d031441042200c4942642e4030012080c0480d298260140c4004019810501024089984e641b8043c1144504054003a4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 501987167 1250 501985917 501985927
    0xe03030a020114090a08030118090b0c0904050c09060904090501060e10090606030513060207060b130b04050c07050a021207030804060c060c03050610030b0303040b04030f121d0d140d05 81
    0xb0015490f054001203440010003c1807000e944052940c04140726a4503403034075583e0039410481003a00a642950f500031038403000d44c03400e0f0040f08050340040c00c4080c00b89143c1000612001140380c00c07903040440c0100440d0620f000d440800c009010070b58011102c42d5220b21000035503409215855002e00703028000076800d1400c21400c031046171007642c0440e041600300010f001c410846080007401c000d402110260380e541d41414590040c0c200780f481541c1002001040c0c00401c90309a1061000d03540c01ca800340040c1d21000010070030b81c041c0c924042c0c0240c10150802006150858461b06041c0a650945030183da413a215000642c00c564014400701d2000c680110402c5800c0c4a10203081000b403d041110382400c05c0400c0c2d442191001d040149690750104801c00e580c1081900c0c020b1503200c800035640c0d40c89161190310211203007021a220740700400d411110a00482007501902903000808010701c88410400c00280301d500002e40310782e10f145d180880445000d20400045001941f03a03aa556 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 501988417 1250 501987167 501987191
    0x5030105031c0e06090d14030901030e01140606070213060306050402010e0d05101505121e070e0f0a02040e07020607020f0c090c030606160c051302030f04030c030e03030a0201 77
    0x20b06510b0358481c00c0c070303100c040b02c00344540120200d01c0100042d03da2948482c08500840c2c60302c480068040c0101a45c040e500b4108200080100012203003aa01880f0001142c003010f0b09899907481c0c00b080c2c19219400043d1241040302c00f500001d80001c010411540c4414210011a200d80d04140c5145444000704004c0d03581040075150409020fa03892030380f44009440701c5460301040c4d260140d60344e4640040804d0b408a5030019030203000014035542c041d03180704c003000342c0c0c50b800340042c4110380c4034103510a04822408200c000407075284140811441d85c030050b1210306107500400a05040d582440080760903242040301900c201c046400404290800c14070282c60a1070070719200c000755000c90619407264880a1141d500603110540c40c0b600c9466040001d0020300881c00c0c0203855040f510b06000500c003945440720101e400540360000c1081040d0009000d900c0704482e103094034003407000882c0000307101d0100d15203030500900d00b030740c0c60040c0300300024159400b0019000c0141c3d1900b00182803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 501989667 1250 501988417 501988423
    0xa0303030203061f0e041d011103040b0a14010612060f030f0209090601080307110f031c0e040207030905011206030b0c0d060816030b07120606090e060328030504050901060503010503 80
    0x180c044c446042c40d08602c41c0100090460003050000d50095442e070030285181d07024000241c0e07540c5a03480091001150380c4048000c2a0011a42620b031841c0031808100000c209100b100c03107120600880c1200b07070307080c40f1066030103580394420a01c0e0f41e50740e000c0000e12099000d1002d170245110314040c00f2001003a00410014800283c4034140b10f8102c140100201d020000845494039401070607400140e48010001d800c20111408140d0580a142449080c01e100542400c2280606444d002404a8643c2c14001240150800100801c25445040c000b079070064545442d03000a416000c550207840369075200080c001580c0c2d5011000c80442c100110048900590300500000802400c00020400342400340040d00d210180401d1400c401040405110b02000c450711b40800205024580c0c0c0c0740d200419180f4035214040c00c0e0300549000c280c041c075011414400015810a00a03814504080007001240c800e02084041c4441000001b17030b0354542c00744050003081103455507070703e0390315100038941 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 501990917 1250 501989667 501989689
    0x30b13020f0102150718050a06021c09031a042303090a050d0b01030b070210020309071a0307090b0d02090a090b0907050c06040b0a090503070b041209060207230a030303020306 77
    0x20654102860b00d00d44581c804800c640d05c6881883c1940400901c1c3c80e000403d501141c00c046d0300140d504801003410790300090f03e01000e1081c40e8a4101410000008680d02a00c40c00000c20a1901e6440350707290b50111034426030410700070091011100044040d841d01c503030700f203001c403e01c83e0800315200070a46403c88241000700801d40f172942e00355600b6038a1030340180050000504c07510004020501081c8200000100e021071490304554a060000e011a9542070703900c1580607001810704c40c00c3c14001c905c825240128999280d01c0405030425044400a030801c281c4120807590078080600540d66250760f13080241401800016021840b50034040080300041c5000700380f081c10055425401800541150b01680041101c030640d119840c14030080c2510b2080a0b1007484081001800d01c4500000c5a000354858030200c2401c1045440595640203a4440c0034051b81003140d041144082007082841c0280c02c4514404070301f01d1500c00541c0e559180d4006400017507000c41001000e00301091612 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 501992167 1250 501990917 501990919
    0x8011418070803070611070804030f29150f15030f0a18080a1404090e0c01031109150c0d09150e0f1309020301020a050706050a020304030206061504030b13020f 70
    0x10500c10308060301ca41c0e0f640320b2480300410701d559906051085c9807189003540c142e85d07031206183d55a00c1d5030f410091f811040e05241558000d40102031031902046101c101c1e0303000900d000c0406416940e04000140c1c20b1503040d050760304881e04061421150b5201e071250f8070600d010350b015036228100b15200314004100102480c1c0420702d01a4580c03020380c00b1407100f00703206521070700040c0d4541c0d080100702c64422104010400300300c0041808500a02203810203416000b640046403090705005004400b036905000700e0720541c0c0c41c1040312940c142041e00b181707c1c0300e000c0c8103061742c6401030843d81c4500e842516140c00300000c7e198141400400040d00b4014001ca2852a04036050a01000000c0c0d2450390804154800c0d240c1081c004a0b1080c1c1d5041244185c4c0c000f0000c6440e400c181030054440e611090301200d901d4a01800141c9002291094a0185405a008200d603584000901210102c10b507101304000300c0c20301c000400110201c42a81c401d00094104140000d510300c144119204480011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 501993417 1250 501992167 501992173
    0x6050301181a06010c1401020c0105160f08011413091202030c06010e061008130f03050406020705150706020a021c0e0f030f0c060d02040e1303090b1602100908011418 73
    0xc01042d81c1d00c903c01120f42e40c1c11408006d0418880040309009110712130880c2181d5003040c04100e22820056242c81841f112516139603440840078404450300d074803d026103441c800308412101c0d00e6051040304011500705038200000c0c02451920b0300c14441c0c5001280c0c200603840007520780c080000c14480a401005942c5802c500c908040c0001082c42e80518000b50411408030005521200740300c0c1094003041d0482c0e2411080c104c07070304000341660b02c54000c05c40580318441001a072810226001c956032462002560b042440d5660b90340085d41c80f8502d01c84c11480740050b02c0d441511911403103007101c070080c0c490090ba5170081e03045c440041301c1d081c422846900114030100c185036000c10342d48001342084524603600e0540c030120100a01aa0b04403414541079001001103902c0083d021800c0c40740280c0390b0812040c0e4a540e880c0c0c4c0740c072070b070070304918803002e808080c2006007003440d10030040d1000c50074004c02c200d8480c10302c41d086852619105003072200c21414003000c107102960300050080c840c03010b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 501994667 1250 501993417 501993421
    0x1a0f1b0c011b08090109030b270d0c11030322030b070e01050912030c100b0310020f04120602072f0a050a0e04060905030406110106060503070c020d020406050301181a 73
    0x80c0b144801411000500a4840007522901daa84509403580180d540043c8402c0b440c2010340c5000c044009210542c0e00d1008261802456041c2c006602c01440c0e455696810911040c1d079100c01500d0240a041901848103210a0040c01400084003124843d00c00c101440c2502c1d6040c9610042d40c00742c0b9813000d0081d0386040424590303000c8116041641d058074000a0b080100402903e14414410b004040340180e9034080c2084d9015000404555000c40840e0140402220504100c2c4280403003000701d10410032082001044600d00c002c1c1d0240985001810711805490390006900e100050a048011548140c1c80207003508810100742e41d01955070b960070b51b05007004601f40741180d0145442922829000904024131074000307000c8564418203803030b283e9a07236550284c0300801c41c0092201650030b041000c03844a21030300989109001994072080c841280760280301e0601d80356202139810945501001c14191024001c86203c141070000340d4240d9145c60070304d5035004203072548111a070341104003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 501995917 1250 501994667 501994697
    0x130303050a141f03060f1a0a0518090f0a080702032b0e0301021303030e0a090e07140123030a0e010902130c0c0f080a0906020303101a0f1b0c01 63
    0x100b2940002e80c00010301c4400541800003a8180ca0b9a000402c040c1c140320070340448581c25005840341550484416807140044002c02c0842c01181c01a190406d4402e0701c110000490600541e422400c400f00359803541603488023440c00c0111840013907070100000202c00c3c0450500b08200d8036020b15900c004501d048aa4400e0109201aa062042048110301d2583c202c1c0d03500f98100c8184203200d42c1c061503415501d14001c0e20503138250076142c0c4940c46c4110300050b0000d40e401aa166155400054010b141c10300060300050307503041208a040104051402003017070341c1840990881d0520301ea00c5a1240b40501250041c0e40342c81010605690401e2800c5005841d410502c0418001c1004041250f1700b0040c03049a02e0700d0708400280819508500603014131034418010710000200740ea804180386d8a550099a803484140e80c0e11140c6000484108032016200c001c0c18a020f601642841c50160340f25030300d0301160042c0c040c0c031218041194a228030103c007040042c00c403090a003000c0b41040707400d80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 501997167 1250 501995917 501995951
    0x5030403030f0f050a120e2506020c0910030204090c09090b0f010503031e07020d05070b070308100e070e12010608010501172a0d0b130302060906010503030d020c0312130303050a 78
    0x524140300329851f50b040b03100a10041c040440c0c2135900b903090324082111440d01606110b030398840c210140c019000300040c241095503407a07102e40325800a40e0140c80c515420721000388070781c42c0c090b00d26000c1c4d65004070b1200b11502811000b580100b4948001c2c2c00c00185d501a2000103a020901c42c3c1d01c108000d2a0318050b0f12512070b101200301700e4090315440b142c000f2500c20549104020000d0207540c0010441460300c00113452010b00039a039101703d56644400c4018a4181806500c1d102511000019a4a8880c080300c4c08440400703408040c1d86902141e125080d500103401031006030b51194014000020510301000700016000010b00341d0a0000c1658506ca42211030f1340f500b603030000390200f0401e490380c0000c0ca0045510440d000c10703515003109044001d604111040b001030140b14040b0f0002c103c0014218180d030001005540382600024046000307502010000c046800284410380101e10b6100030b4a11800c2c41092142d13000f017041c40c005040300c80060441e07000c5d9240510b0b1858610040b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 501998417 1250 501997167 501997187
    0x307090608130f0305040e060616060e010e0616120203101509030507151803020303042601050405160608090d031d1f15080a08090a0305030403030f0f050a 68
    0x1810814560b849459a004015010034030142c1001014218041056405070042c012a5800c200c0643c00343c40e0401040300901c20360350600c00c03841040301810b0115509502c00d00d00000e1800c00015904002a500c1c0d045c242e084807141401c0b0005c8400c41e07a0b55811030061564595101c204501e5890300765003d065035602800798000440403014000100c6004001070400f0303541110484907003e0fa11080210024000d032140c000140c070704c4001c01d000707251005400c1e0640752f00030701950406040000103180c1c0d8508983d1000d80745115100704250840a100d514080c0780914050100003201341d010f546660301e607030b014804003c00070003000101d90740800c4240d41c0750308900d00031942620300001507030300c0100b42d0030020305400f4001c0c0311410507020702400c00b041c041c815018040c041c04800107000c0d800961084198a400c00c06c035020003e04160010400e04100410350b5052641720b403519461500503410031404105107100488509800c83c102d08014411440c0807407900c1c2c400d500c024208884d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 501999667 1250 501998417 501998429
    0x1002030c1204081b06010f1401090b030a1104090905060f07020a0f03200705040b010c020d02120102070c0b090103060f0311090a1b0c020a080a02011407020a170607090506030709 78
    0x36000110b010003030031204507030b0030080100e00440800213004080c0c1e2105000e114180303000031341503c0000d01d02c005e210700c42c0c000383d41611400006484c101d4215903560004054005032990742482d020041c0e403903006440a840c02001c0020300101c01c1c5010f80c5800005001c2400e003846032000c001c11aa4006070144500c1d6101100c1c0608200398542a600d80c401c182107042c4800c000e46441e0704002000030024101c03101200d023400040720f00801034580001c1d2a01c003a4102a03259402005400c210f82010382050a403000146030520a46400c44125041d0b0064020300e000014810307115a40b501070074014090041c41d50140303d240d5500c0307a43c42d000300c44255001c1c55030ac0700050004070103a4880c00107041f60100a544251800c3c1c802840c03c140ca0004078440e1411850100e1140d030001040b02c0b18940c103854060b000ca4160f2140e20030303a004100126070019243c4804034616503002c500313801d4661a5001001d541c145110050400266a00068024007051040000155004203c0411295 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 502000917 1250 501999667 501999697
    0x90c020345061606090b0708070f0c15020a05030708010f0501092c070c170a08040f1407032d0809011d060705070602120a020d050a051b03030601021002030c 69
    0x50407401080450062081c0780d80400d5084411000b03100c0d843d04502d40c01c1d880b0b515103580307030b6452032415641a201914540000341c3c0e120507110307020f801484038030102ca0003101500041c0101c0f80c54003085ea4040d071a000700180380802489225900010b51034050b04040e41e02e152a5814500001c0c00180d0f544601c01c000302110303c05020400410b11102841400110708951510305900003078840501c0a100300c07074180304e90a440340e00c070001e00d0640720902803d07a00c00c0416203540c0c580d4003010072840c50a4070086228280040c0c00307403041003240c0080d4466100c118189900c007070b4080c01c444200c03c2c103480c103041c042d4820001030101c00842d0000403090070000c6160045a98482002c454010400d0b08040c00040020510000003040012101c8903422a800440002e40c868058064000070902507480550380c84641d074050409045c4450303080c0343c81c50174002c0c00b07150141d80e441c00c400e80c444030f500000284080d55034144004405950002c409601d1401c1c42e658115592140d08090b54182c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 502002167 1250 502000917 502001047
    0x6010b0901140906071209060e06091c150507020a1a1e150303180a06020d0f050a17160206010f0e1f03050a0c050414010b070b060406090c0203 63
    0x3a03204d80550b445c2c1c2c3c0d0064100d9500b2081d10002030454141070050601144281c24100200c0c904102142e030701807030150910501c90344144106551415a0404480032105148030708000c410522615200e0489a40140204984d50506900510000040b0f0310f1a03400f0f2810009903512900c0d13070070700b8958400407085080d512410f500c10a250026902949400001000b0f581d00c440450b640d00303403c80480e003052030743e980e46c0c409036540c40400010801044404d08482000c44c051400b0340015509814a6030b000b06e07100700240039041040314450420700d0740039080040b840d410442a805400c071411800d2025081c51101d60f500c034001087d48260a205100c20100034004000c0e180086500404480801103d890140495840d5010b8240114074103501a2510440204218100d0b0b407031009242ca400c2e82600e5040d00035800408e8141c01c103807990000281840310303100b40840c1e19216405543ca90f440700005c00039004102d1a1104200d40c1401810451045400f61012425503501060444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 502003417 1250 502002167 502002169
    0x2030f130503090406030c0e0a0603020117040206091507030815010c02120102041a031602010911040c141321080901050c0a0b0117010509121b1005150306010b09011409 74
    0x140c483c00c62915042428040b00004102d040700c188800d49070500b50340c1740c2e00d0f44e9103041c1808036146840080d001034040d02620300501f402800f460b401c41d0024284074a031903c1a4042088408440c4806010010000302c5c88141980700d010301d41c000d200318240180311201600004c082551640c80070f44030f140d0411034141c0c040c800754116002420318010400c404000b5403149002500100c5078408519030000398100c1c1c040c17040c032030300c40c0290303021410100c05138103003061000415991403000240111410201d40d12400c920140c400c0c4904400304007200b60802c56442401c4c1c24200144020b1403d100408000911650a455007044280b030440e48400f01c0040041c9070244001d4080c00450031000081600e010702280c034100340c481000240300c9a00c0709540e880d600c1d43c00101c20f1200740c405204181c8010600c018038802000131104480c00070100e03c040e034048810a80741e0301809039446525400c2420305105850042c090f006103030f400e103980b203400a00050180f0b81444c0e030309803000030b610741a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 502004667 1250 502003417 502003423
    0xe041a0a14060706060b09011701060804031412041103010e01050402090a111603180e070c080d0e3007030215060111010e01140615071709130507090902030f1305 71
    0x102a030001ca040c00200d40e01d03032241042e940b10302c0b990750016108207132704982041052503c034102e401560303c1c070750b00c1c0e0303100d440440d0300b40700100d0461124131042026003800d11494031000e0159020f2007000e80144403050401d4211100c40c885450703540d0402040001603070740e0580b0345601000708417001c10440706200c3c20612a22500d0403071484040c001140c1c005160307010341c41403e420181078807080c1950315801c8030310426a084503a400056115011040020f0444001d0000c0e070004c100c000c0360081e42e0020b41c504143c0303400c0b4802c41030840300d030407141881804500a0707031000c0c2c0c5d220468505215074800940381d51540d00607900c1d0401304000300303950742d00c1007044d008440003e0001b000040204024280038098400e000d08210074200007140712490091031100f5417003190403119181000c0e035030303e010305030410214804244405000702d074903a455a0300c100042c20015003001030a840c3c0808050000b0600c0d42005c5046031040c4104184403808903400c0c5d40100008100d2181000140b5000785 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 502005917 1250 502004667 502004677
    0xc1707110a030f090e0606090f121e010606030e030f03040c0b031303030b30070f180608031309090c0b0f1b0c0315070306150e041a0a1406 61
    0x150600c10740c1c814600b4190312040c02c82c401d18169603444912903459400389a202c41c10b07510594404030800040b51146003c2004502540300030348804460010001c6072424042c400460b8100c0c211310a03c0c1c151030030310a00c50071010b4800d506041000c403040c1443d90359240140c0c5400d001202d00000401d05012004440384014429110400c0ea64540780001c07040c1082c410b00110302182c00c0004e4003210f0311300740c0c801010180d455035032084840c02d54a14803c058030041400545401000004130b12051200c1c0c20002800c4011000000320340e0405010742168643d0f40b207520150018006800c0b007103000e43d803440c200ca04039000401d42d10041e0030122038081e141c1d4440840150002810000c11340c00d00040c09d04000560760701940003443d1842140c4801c0040c1d02c141d40368102c4125864440c02007040281c004036985000110262101203100c4030794406800704012a0b5012410082d61506008a01c0c2e14012a480c21103600c03100780105000720300705d004c0c1c0c000d201200c02d0140f002d030300c40e10300b512 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 502007167 1250 502005917 502005947
    0xb040f05010c0507301d090c040e0702030708181f020601060e0a030807331406010c0c0302060c0c0a030c03050606090705120a0b0603070806040f0c1707 67
    0x2c40070041c42d020302254044581152298040402d240c003a0911624546414850442403402c510203102e0445001c2441c1c2c500c00c0010640445082180d01e41a034101c0c07059081ca04d1395562141040c880c030b80340e01c0004141d6030440d03004108550000307030b607442039400e210003581e00030b0561841d000000d06000a020000c2280141442c0704500003980010064100c80c55510313804040241c2c9402d12600c4425404040d02038070b010410000050300f142c40c00510b084007620151250550b11051100320b510140b0303002074844d20340058850300702000c0650b5821190900340822500e40654134038a40d03841c00d22000c0d21466001c680d05c59420824014120b0360b00303009105052840d02c0e858803041d111510301041d1814400c890003d41c6d1804c103440d000c0d020701415113442c1e08042a000c413242c044940103003a035100a0721000303460300503210500514010b19054562a100b45800410f00003107a4501084c0700041d414420200307242a00080920071031201d4a851080076502c01e1000e03034020490007218 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 502008417 1250 502007167 502007171
    0x1120e0318090711030702060a030603020907030f0507030513120917011e2c07051807020f010623040b18070f0509100e130e0304300b040f0501 63
    0x900c0000001d1041203400c100101c501c0101c984840c503040740c140b542e10b03003640e0403039104120200151030700c0006091000c0d50b0303103004203c080c1c50b9804200c9030b84041c0e80400100f5115012402400203a005899110442e0b02d020043c0d0b217010203060144a0120328058250441e2481c6441c0d0248500700d0714000c1d0820728040203042c1d00b0001c0050081c04420b00c0d64407883c034164031440c0780305160f0040b60381c0324a079004038418013803080351818240d051100e9648141d01c519100012130703444100c14100444070142d040e81040c6000b0700d01904000d1310755022401649080018024800c400084c2055001c030540035904d410000c01c0490010404500c1c0c1c0e913400b840c9010041070303510007540d003148549991b65841158200c00b0600f925107000f81c0f2411540200b4050200781c40707511841c00d101801c3c0000700355036000d801512081044600c40700148040790400201032020126106030301c1c021003003038818148007580100040c1c01d40000f81500030325806c00180880c0620548950000c6020b03085802 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 502009667 1250 502008417 502008427
    0xb0a1d0309151323030d0c020f0a030201021b01050c030c1c110316030c12020f07080708060705070302071d06042409020901020f010e06040b010f120201120e03 70
    0x45a900e0708440308251044000b064041c0c1561907400603030b82078540d901d201c1450309091290f0b104039260340d13034405100701d010340c0000a000c1e5020002030108801c41c0c5c48100880714680103002c41e1b83c1e4014401801541404030400c0141d900045103e600c0c05103400210580b840c02d40100c1e45403250340c007444100d12000c01d405007600404592600303002d03c46940c40035900300c050310a071030710020a40900d40c40c0c1c2090182c480e8a10f011008a0740c0a4441e141c2488003014030b03618504403401622184005910640c44100b00c05010080d60014043c854010300040d131400f1681c42c1d80f400018112410000301080305001c06000f000006c0140621030b01d0418510058000340d000004212001c0f880b0b10b0034915510008030382c40c001c004400d41e856440212940c10b010b00b0304081e41c003072015241148542511030130080d1080c81645901d10101c40644118101414003400340b070410380064550307160718070082110310007454111181960a007003400e0180082100c1200504000c015848a03010000f6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 502010917 1250 502009667 502009721
    0x90c06030c0a09080a0818150d1505030a0503160c0e070806090601090b0313080d0603051b040c021e0106350c010f05070809060408060406061d040b0a 66
    0x40500751030b806581d204032803030f0f65881503580d58040c502005400e01c01e08011030801c1d0050800b80521620b4007501494001032440442c500a80c0722a00c2d082d4010b1765584030141016800c09007000600f41103000b0b02d0401c0c0b06880e800d8803885056094000d0a500b0540f090400c2141c000f008000d03c041a103480761846c111388060990501204c16070300c5000a00001012503003d40d50117016079480890080c2581c0e103c4d000c600074000000e00c141e0b10100d00b801400d050500743d004a0f8003a40c4541c0c09440081a044200c03984116007425141c411820441010300743e0360f000a6042c1046101c00030000441d0900c140740e80140500e41120f00070417264424030185107008104044241314032028005a01c1c02c4030140e0351110600f02c103c40c0041c44611502c2e03141482500074080303440c0522400c074502140c650000d40164410307400100d10340c11a504000074030100d44200700091002d5008400c0200140c18881c038042001030000f025401854082100c4041c01d500c4030101c03000b4000d40c01e19051800d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 502012167 1250 502010917 502010941
    0x2040e03040815070801061803050313060311090603070f1b0f051005190c1716091508040f0609020a0611070609120f2108010e07020a0308060108090c0603 68
    0x1010b5421688035803815104801d00403508240718211956440c2c03826401d281c0102e8142c0300720b40c4001c440c255120700102c0803c105200903c083d0910b0403070300c403115140c41400b0302a134035402c502e81d120745001d0140110031b4441c44c00f100d46c849114504030070b8a80d450035094030401c0c41e981d414504501720108000410444158011034940660203c0310b02201a05284041da5411901507000648005042020015a800058041c8510308143d5840c0e42410303140d60711051708a07a0300100c0360300c2c100a01c21050300807440e4006424003020040107000c101c138001c0c0c41039102800c020311100e130180182050210b21b40c00651704e00d6000309440e455a50f2150020f10110502c0384101c25401440d40010368a40a55448030803284081d038818004081d6446122401105a20544d001c18403e42200022150b9548400c2181100e440e811041e5043c104201071120006207400c05540c005052440841d4200e130406902c10707400d107841001580c1d4004694142207807445519000384010040c400d5606642c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 502013417 1250 502012167 502012169
    0xc0906160f06021e0a20071205060105040c0207031110030605040903030b040f09030c0b0406110d0207030e01050a081b0d1e0513020108160302361905061602040e0304 73
    0x1480c04e0080001101c1141001d201d007901c4040418a01601c00943d2a10a100032005580a20aa031000e07079481005500f00f40c00b059045a0a40002d00140f0075450148640c20240c8402e1004062860440c0d40310004c0031034240040d84600c014810310202a0301c07d0f003008000d0071029105000d602454503002d4040c0c880e4039080d51046003040f4144920f108075100f203d5445816689040c3c0c40100d5445240340000050002d8513920b4407410201c2452043d41c004100d0301d120154016038401c0c40c1d040042403860540803940c10060100000450554040754081c1c110a002841c1040542012440500c5100e102c481c06062810002451101c150b89034444000090040c4207002c2c50759803c40420102030010780081c0460144804110f00c3c000031617004483c20101d0800500e0400c0c107505a0303244801c1c000d8101d01c004000f0503602224001e010f299500302009540c0e1810ba90803981101071495030700c1c0070f039900840c40820100c80c2c00303505241400c00d0980181c02040b00e1400240c7c8030382c0707907406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 502014667 1250 502013417 502013437
    0xe0f12100c110a11030307210e040603170a110d0c11030f0d1808070f03120201060b0306060c0a020d0c082b03020d0e0609061e0c0906160f0602 63
    0x2400560300d10240c0101002e50860540b50040c15030682039030341d5801034503151554141c152006001460000f0041c0d082e4113544e141c0034810110304209207030014006103130020030a0103107080500401c006a00c00c1072040940403a44e00701c40d100c02c22a14221014a110740d40c0301130500c01c101c4091009504030701d0056981d03019248000c0340706040300525540c3c4683c0c4000501c0d660240340760460061049514010314451001c40c1051280e030303045000e14142003034004020045200c80c04000b0400200e06c68401c10150340000c0c0803491822122030344a02005280d00d0040100040340058100d051120a0410b84e0060084d202042582852820b50a060240704214402d4051480403103105180001d1a405502040c1114441024048001e0340101154014a40d00ca40252107240c04c203011301407081004c900240094076000101842000725480740e0b4840140341740134015039114910844034080303026100c1070341d15003031480c2c14903102c40c40d07407000741040810b02c2241d001c10000750001c160380e0300c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 502015917 1250 502014667 502014671
    0x81306060906051e2b0b0a0218030a0c0501180801050a020c07050604140f0409050a03030902010905120618150106020a030905060909061e100e030115050d030e0f1210 73
    0x45004001a8264130115107590007040180300f4007043c40c50f0901c1c400402e01d6400140c8040c5e40c13940e11816105025101504010740101d41d01c41040d405070b5800c610108101e008182031445611510b03c004058003e8504015405403007410f00d010903039804004000710002044140741241d1814025000303000c2040d150f002b5031100240c18a001c00a540c107842422035902c002c1d501000801107203044090310250000d40700c049a8000c11814450b0140743da01035140442c2c0b5003441c0c0700061130340820f0740203584a140f25020720b842154001174001d81c0a40c62501d0b40c040c10941040c1180303031502c90750544002c83c1206c400460629408103414000300e2180e103072540500d40700d00c00c010315070141041c2c081d0440c4211000034098541000b032040d01c01100300403105800004c1012510200000c000c410209000c801684240d0609210750b6038000d885442200d8414101000601c0c4102000030140c100b0148200c456095500d4a07401d00c0e81c10070040078410b013840d4200700035880318911103070f40c00360718 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 502017167 1250 502015917 502015939
    0x18050a15030f0c0f0621061215051602150c0403232b2001290907080c1b102c070501120207020604030803061005070f0308130606090605 60
    0x3011111071303003080e10302e651a500d07107544c00ca54040c00c1040000d522500a00e44480e40040d450310b00d1b0541521540c0111040d0300104282c80081098440160840070350b0b07003100384a1105150f000c5a8034001e2500003000e24a9078503030f0080c00c8034601568001411030840e241e522100502140d0758408045000e0007640c101011005500c1204d000c0e6409141c04452100d0380300190510070716540c0d100500c90a02085103c0c1c4021040c1d0031541c64401009490302114014510304940c1290140c0d051f0003110240c0701d900c1c011100402080b0f0240201c000007501042598600020307031030b12210a48800c040310055840c0d001c2d0b010107403038040c50307240022842d018413041080d5034a94104822136004000c11019203080011540c4190199207542240e500713214940c01a43e40b08001c00c02980a0060300392217060110030420301d98140112801440070800c00c00d000103459a4413140700b15014104070340155a1a032800c00110b400100090103203242140c00700701c8040c1d03540024141e42c0706039041d01e851 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 502018417 1250 502017167 502017179
    0x112060f0f03170301210212010c03050108151608060d060515040b1905090702030f07050a120203210c07020301181106090105031f17101518050a15030f0c 68
    0x1500c801e00825407248059071b0248a003000e0040002031091015042c00c00814201d0140790840704074100200020740c4031b10040069120800013644884400b511441c041e00700215080400c400c00841103007840804030000e00d4941e10b00141260f0541c200701d0510862a00900072040d2008021107203105500e00004c80081e42043c2e0041d0f4091103505050301e201d207051108001707007003c0040100c011403004000b1000e048410f40090400c4502c12402045041103524011110a900010348000c42d80140055800c04520b20703c1d91091649411100095885180041b030091107000c801039015801c0180d500340d0060801c01d00100e0a0041c115600c0c0105041d040103400e104484003070b800100d0034404113030300130000711040965a50125004246650310000540c190601d034040c610550420f40030f8002c1d10403a401a103801080b5040d0400c00390b4107010108410180d9003030303182d40a998a00000310301e240e0301c0e4484010800250340003411503940c3d181046000540803021030b02a0302408001030a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 502019667 1250 502018417 502018463
    0xb270d0f260a0c0c330201110d090507050402030c0d1103010b09010813020306040807120305040f0b1506031617060a150c0b0115110d020c0112060f0f03 67
    0x101140e1103260703915003181d111089403c4100e05009858103110329900007032006a661002e1104c441c01e0a022070111081516031103060309074070001c0207590400c1d4080c41903c1e045400c0307a103050180400040c1c0c500e00790070150f240030803d405c00c0f60020f1001060040b0070101501500410201490501201c3c03124070044002e40000e00c6514405181800f14144560159003c03071703440b0101590741c0c10086401d800080c98010700b924103850800b000116081804a42d8a1101d1840407d0030140420300f0141d5458515000701d02c070160001008001007448020340b180841d4483c0e5009098503107908000f40700fa0100044080c07800b010030144405044d603440e85481c028851200144003003a51494180080481040d20010201300600d4805010018001c000c0302c5001e4103c0b1650002282485080501042400043d00405034050344000300305039800034006410060a2822002941070200d02c140a400550408d0005000b1118040750032880c810071901120300414082490400072110001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 502020917 1250 502019667 502019723
    0x20a080114041a060913050117060a2a0203091005090a050405130204022109010f0c050910120e01090503070302061b04050402250506040c09060b270d0f 67
    0x4207000f41d9070341154140b41a401030040d14502a10305100000c0221600003210f100741c001c1c00c1e0001d400880310300145010480c03113601c0184501c1c00c100741c07405425000c112103028503100c0002c480d2503110130450b500c2402519401d082c05405605083c8102c9405011070300820341040c014050320400283c0e43c0b03010f00809000b40c41c1c20303000c90f040010350303001c0c84081e6001c2c0c0368403201803002d03a18107540050f0b85004244108110800018280e40700110201515601c41400c070800006020f40230490307480c0310aa14210030f007414850340401814900c1c0000e083c1c60700301c0e83e01551900410348140f22021004104030f07407080d4203449480e903d825030001d005450030040b0100c07490500003031150303081c42c1c0d00801d40300c0b047c83d072156020710091b032003c2d014602030401120960800010712040103018140702000d0300c00964188440750801e400c000d15809200c403003070600d1300400014a00c00c0001040040c08007005801025060140e0034101001c030701c001003c442c81c4015050000f00000e89240c401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 502022167 1250 502020917 502020941
    0x50c0f0405060a02010204030c17010c0e03190c051017010f030c0b0c0a020a08011d010b011d12030a0518010f0507020d14060112051c0903150906020a08011404 70
    0x60038541090144031098101061103019590f08100100110301e410250b00001c0c000516091010086020890300795140000c590043c042951b29201c503070755000c10449034400c200321b5040410700440c208ad070000b41540d030150783c0114407100d4690500d03034041b4441d080f00034001801410f03640c0e1410502d99110582c44040c2c509564142c0500407058007000914030a07110700c080302d60b034051a03000106001080c0e8440c0c09160f54811408445090b001140b11411050b030b0000c0208507084400079041c1f84510f00d459049200b050344546040d0f036103420616590720700204498984511032400341169001030400881022428401c50056102d0a480750703404800d40c0d981810300c5c0003582400a000f0221508507a0a0000c507085000888200480f0b8020041b601551154001030704005040010078440611042e1001c00141922500880740500b207079802019940c94000d00c60340800180f24048000381410300010305c94900607481403c41b4107035440303104600000070807501080304a4604885c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 502023417 1250 502022167 502022197
    0x203070e0f070831031205040809040b06070623011401021c0e190906090902030303160c0b1005090123040b010c0f06020703080c040e040b0402040912090306050c 71
    0x40740d65128460240c3c2100c070314940c03409407a40e240f003030840e00d210100c1c2d40407407035214500d084c09155001030079169010200782c0401503800d0644030700705244521085140a1078856a6184103500c4c0d007802c9860958205400f00200f426110010f0310000c3d40300d00f890449a1014001300f041168041c0c1c030350071107034140c008000b401c90501c03611001c0365481c00220f0038006200004221510b0740d01040070042c0c0c1603400d5030300f03c1e800d14513194100c841c541c1103110000d191204240042e1800021603800424844404452083c0d40000b22544400100020108042039082c0f01d01344041c441e4400942c1c2085920421981e00c580e2111841810300001454014402c3c001000605103544075481e0100189044032201c4029280c040810502c0101202c41c030303900285540034194080300c0a82c00c01d00d007448282c5400c0c0b0302050340410b9540944003902001000e404901195296804a41c401c1d611460812000c821004050521209840300b9555141004e0000700c4600406c002c80d80c409c0210140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 502024667 1250 502023417 502023421
    0x40b090f0703051512070305070b0906040311220c17040203030a030c1211090301110c1506012c03010c020f12161e0c0e1003020603100b03130203070e0f 67
    0x302c002e420081d000840b03000c407291040803283c407201036610520180c000141a607500d10301e0658684003c540c82201c0b2101c0520000416588080485003200d4002c81d0600c1121001c0000030a0002601002510140910000181ca2000360440300d09515541c442100b00810030001030191041240c000754140c008001c01c0802034003950100403110f1482c0390080001552018480456622591040d5210300115580010340341c24000d5100400f408407205050109104845c0c1c1e59992048508880c82c0c001e1000a8442e40700d110451442400c0ca40c1c5003207415101d00d0079804d01038002c1c2a00c2e0095083c00c24110080f40000381c4902074810501c010000c0c02180c6180314001d401a40e050034407503070300020030320119180b00f40010080d0760080529150b495a86070204000302154851254070b61180e04100075034903070310507590450341c0640d400b40d030b00e41d10b401e1102000e002c02e4014900b035000c0032007400015200301079442d0160f8800d800703c400c1d06d515000c04030b0305458100d44100c1302c0c13000c0c500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 502025917 1250 502024667 502024681
    0x60a0606050403060c110d0201090c05060c0d110a0c0306050a0b01110d050703120911100914010c03030207330504080301090c02032704064506030f02040b090f 70
    0x100c00414422181b500c11241040540b07441c0c14500005501030050391240c900d4014002e54800c80001444211400740c0b6060044a07444d0b2141b401020103002e010203550b02c1c03403007c1424007200c401a84d101544e89a450345a203003400c01001c041d0b800101c2245080360301b00055000d0344019015981d924002c000c000c0070040c0440d02544162411400c210038000c008001c50414020540340621410700c0342130b039160308024080200010600e910401150362400c024070102c250360354400800070300c0c2040d0f40e0a820304080c0d000e8403980d107009010750503101410040a00c650141400798004860442e8010315500d9500c06440080c0c5014000c2e200400c0100140c002ea41d100200c9000b0310b005982c2005030310f040c0d00ca40d2400c0912115840300b0340a505298501d040e10074200070f0b0030590b843c0d0700d003e03480c1a11600e842c034034411800710b504000d044c140708409101000d801c3e4006212010b0000c0c0340c40b880c0c542e02d5442848012400380b410041507107203514145030454418039480c0426800f075683c0c0c0c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 502027167 1250 502025917 502025921
    0xa1503020909010305060a0c051206151909090c02010b030606060d0b090a0212180a0f0813301a060a0302090a05040c0609050a030219050301051008060a060605040306 73
    0x115400a05608206910242c0c4030511a070b80214042e00250042d8034000d2054020707200c3d454403060411008021240b112400030066075040030b82913501e45c11440c2031103d180401e115002c0c030380b003030b0301ca030001c164880591204c07a0703c040e20403200041c09900c101c640103900f45c840c46002d0aa05401c4840098450709101001e800304d802a07c00c082001140c04002c86c1d9080302c2a241900180d8001441d0711054125141c0c0f079070822048c0c0d4191b40300b51000356880d500e5075400351000780358050303030b1034050284141c10302034491041505410a140c1940c0306a403614200e0302c2e5100743e1f900c00745061261003240c001020030480c1500304000036406000c080062000d40802802154031403495500400944c4400800710700c1580ea15000107100c0c00c0c80d061071020042030368030050030800b407200c00f4071807500c903048008101ea0781030384c0480c40700c890380110b101004804e0b0010b58043d0f00c0d00c400c00412000c0054501d0803103880005840154880544031400e98000b03015140204100304010000120f480d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 502028417 1250 502027167 502027199
    0x11060c040b0c0705150c190804060c060f0513031107030b07110a050307060212060a0b0d020d0209042406090b0f09010c022e020c0d03110f0307031713020a 68
    0x8001074a941079200d00010b404040c1400c40c44a00d1030010584031040d8200f080342040b80c9007404407081f60b02d0200c2d541c0400600c100c0c080c007010044504051020040d4030b41003040480d0b4054800e110606c1d106407030f206000b10b125000c1c0c000480c0426030b1903141c0310101b03110060300d80090500c01c540d038500c102922a02003840d29a00303944610a454000314500340003420b29184503802c0540d440e0f0007061070301c10354180500070501c9640030101c02c0141405031412519814440640541c030350502042d908028040d1210b12030b00a42403a4418040b081c0071151a0050111140c501c0303800768444808441c0001c56001d171000d65482003080521546842c1c020f0180036005141c01441c0c08091b40c00304010034820f484914078030025501c4d180e00a0742d854042d038102d440c02d00c020a23860340210000b0b042a4907401001d010702110001034040d509003400803903054a000710440e0b03982c1459280040020400307142c80003007030200c80086460030004640c0980156001440d10030701c24100740b04260484c840d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 502029667 1250 502028417 502028437
    0x2802121201050f0105040906030507060e03010b130c110f07060212210406090812060102010b04150306020906090315090706090503060708090f0a03090f090b0616020102072411060c040b 81
    0x10b00c00051100f409005000107182b1400190140618041d03019010346501d5080381d01c01e904225141b6133a8039001c0b240000681e80316008a00401d0040060320700c0c50f403003002c69000b4002c401c41c04203042c0c0d0000b41d034400c53314140d0880f60b003020b618641100d54001d18201d0680c484a40014007200c48080d40c1d0150030502401c000281400d071543d441d035040d031014000350101d903104000c2100710342c0c080c4260105c03050152000c1c0401c80c005100b828047d082408002c0030942d021403a1042c40d00d40d08282c1c1c20700480134003162280c0340407440302846030714111450328191040b0341011905038030403c5103400b100c90240040c00e180d21110003d5405c0c0034018001c00c000d104007611004ea24004000700701201c2e000380c80c1c50407014142921440c10461a410516440b81001c0840380c41c2d4642e101100c20001040764a8403213007a040c80102d04101042c2c1c880c115400e4403d80380558103c0d04261000c0750360355a200e0546e1041d070548003a4442100b10b803c03441e2500309100800010904400410020741 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 502030917 1250 502029667 502029677
    0x3050601030b0a0b0a062102030c0d1d12030103063c0b190302030709060b0f0a030e0a0c05090a0630050f070303020d020102181003022802121201050f01 67
    0x8030004c117011002c1036109100050b1203100481e100e6004c13840c0300d0f000c1c41900c10154130b503107484d2000c0622407040010490440e9a903040b03000c494180e95800b081001008420b89001c2600e022404185070000e000c143e414926103e007402070020704800706c02c540c2c031001400d540e4008120590b14501a084041e213800c040c0c81d54021404c0c0da50b0180c61086502100d01207010403415801490f16164290304841200d51411000744a03240c805c0094801085814070b02c0d5036038070584903003107020f04000c80b50041c1c2d41c1b00b0060300000300618001a030382a0758040d035040500c3e40d20341c000101a1801485068540d80f1402c416070600800741d80860705c2a54252110100d00c1400d50300d461415070910301221854010f032000303104066050041800150360340c03000307500302200100c040c00046020101e603403003005500f0b402c0780c1c49400394060b14280401d110300344101c0da580b201d80c6207080080303103070f1000140607864030420b003100010290780d0007840110450141d40c1c2000306200a444e130303045180303041c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 502032167 1250 502030917 502030931
    0x150f040609350c070b090621150420090301060f030818190501050d1803030605030715090e0a060e040606050a0e1e0c09060f040f060903050601030b0a 66
    0x8002c450007003900d9600703141d0b40380005001c40d0000c0141c00400303500e101403582004001d01180c2c3c0010b0078401e4030030781c0c1344940d640e102c16000580184107082c4030744a01d0250048002040d40710084040c400e9803090100c000700c8207981c04210895611461004e00080c9901104800d560341c80040c0143c410f003d0b0000941c262101d440318217a189a41c4219a641c100094543e004041d210410b80301a00a5400d60b50310354800319099030700203c90098030f0400c0800302da40150320005400c5000c1c1e60107201d001a4460040b0b040040240146004450080c0319007000080c1d80125601350f07680c00e542c0f07a900d00c2003490070141aa8110030b00900f0b0002001e0700d0300e002045c0e903035203004114043d511401000a0661614003404143c060342d41c0000708901e00801017005c80c16022041d008482c0c41702005065503583c0d841c454805015201c0c2d07140e08284003045d1714110443e00c200410598031038490040c522651190b00320340c0c0407a94000200b654006e000100001a4606000d50308030360750140204002c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 502033417 1250 502032167 502032173
    0xa0c060605060d0501050f090108060106050706141303140c030d090203011122051c02010818030406090807090c020d0f091220030604030f200607020106050909150f040609 75
    0x40d00450f00c9180202e580d4001001580f40143e43d02c604d60009840b000300c02d40c58801c0141d26074a0511440040c014005000020400183e006102200742d282d2600300c1403c007040a41800589030004801041c2000704040202c009030080d9919055500000d614180c0c000c55000090200080103c1c4c140d9203600e03041c945501c01e40003600d855040041c41964032540c4106a0f5505842907116070b01461502501e8030b0071821840a543c41e240d028201084644c4804410f10b205000706001c17207086000102d804a051903101e0314403000c480489003142c0d4103c0d2588044812a424118044096401004603580c101e0264261542104180c100100c40d40e40d2a4a072260000e815001180c0b60b8058038a0161744c003041d645101c0c0c2080041d001003856103400d5030007502011280280105200740c483c1103482100c3d100001100d9503c0020a81d000e60030803e4000c0d01030841070043c48d11a11409001507411540022401ca400032295038818040d02c4141c442c0c03072103080141c000e844036070f1141c54030808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 502034667 1250 502033417 502033429
    0xc021c053c03190906021203040213060602010e1e0a170d0e1629030901060b0c06060111030703230417070e1e0a0b190f06021c02030a0c060605 63
    0x411890000307107a507000c520383c54204000700b95200100303022860382d05210b800da0002c2c00d24020040041c0e002c0d82c4c1c3d00c8500010301c0040314642000c4003941041c0010038525419040011200910f2040b41c0c1c0200f22090050500704001030315403126805843c0d001d012903210280080000346913007004d460041071015031420303503002c01070f01046680200502d98807540c1c2e103141d850050103010b4600d20798401410034202c1240b500300b00b02c08050008000b260039554298407507002082004082c0fa6a60309055002d03480d55421a900c40c08210542c071462442c100110446214560540d02c0c007c1d07030200b1410403290031070078100d000f084850522020543c001841341990301d07200194000e00901d032504a0200c030f075000003407650080c0c00d5108401c100c0c8100c400da1f01070300b001c520000803070410359400201e4138025008100c1a0031400042e00054008154450001510030315402e0702c0052445c18072190508030a1464400181e00400546940600c10860401c0f0a8410240458090b5071100010306c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 502035917 1250 502034667 502034773
    0x510020f1314130204060e2803060f0e0102160602071e210203040602100209060706050115020c030d05030105040b0d050f150117030316090305030a0c021c05 69
    0x2001c0844410800603d80030f5480003101c05070070002d41c500303420041c0c018a50802c0308881e90042d50700e40c250440d094220b07015040c42c0308070f0132849845223940e810a10b015000f9011000381c400d2401303110103001401030003150f203440006440e0007101c05159039036038002c1d80403481c141c926940403101d0798034100c2c651a0102165000c0d020007007055004c1040c02c402012041d180c00c0c107641c0f0800c0200001c90300441c1c080440d40c2260030060b00c6407c0000403030498401c0c5800109041d01d00000400c1802c2680d0003d040c0000707617400c540320000309805043e0380704460500c1d180401c1f07041c0300420030341c5481c4d002130711040005482c1054070107059a9051506d081c0740c66140b002d4104103507000b0bc0e60350303a944403401044030601e1341850b01d088110302ea88911014022040c088892290b0103049070141d03075000c00460380b1804480c1c1e1a41d0004004105000e8108102c0c4107201c04031458460f00300c4400e040055540001c080e003040445d0039200c1014070003c28803a4440394074014000d505901004142c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 502037167 1250 502035917 502035929
    0x509010c050a170309060603010902090a0e030c0a080a12050f041113092001020303190203101706240307090209042301061b080901030f1d160807030510020f13 70
    0x240e213905010703104c2820040018070890113603241c03035030030005a0341d0503103041d07005068144001644c1200c0000c3d00e00b144203001c80c0420a1144070a85020091043d00800c03510820340ea50111410b00008804251502a190409c24a2400c0e0116022550030fa400503080309006000090082c001d48509050303419504c1c058505494030015a049000c188490b110030020074805549149041d681254910061603402082d1310f901000088081165481a001800413500354080440c24808551307921135046411003c2c4018101100310800322503040303001e40c4c000c010050695541004110700003508441c0116a01640342d94480c59110710028000301c016042d581c40c9290340d81012006440c00b00300d004c84222009042c044100459103400540c0d001c84824a03011544100402080003d40b07001c112030030444e6a4051810041b0710000759204401804041c1d4200c007503510701482c2d443c1e164500c0003502c250000822040c034070030554014000500303035210042c20501d9516050510b041e403908070b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 502038417 1250 502037167 502037213
    0xc06051e010504060b1b0705060c01020408011b0215071407050105090606010c0503041e03080c061506040b0d0f060803030405030703020c030c010c02090402031e03070c0b0304030509010c050a 84
    0x1840c004204560078054502520140462842d02800340041d1041ea112002da00700c2020a440400c0814070040004040c010826611910002c403514000d50051180c2d070700648ca00801f0094005194102c84a5018290090596002041840306650900500f03120420502303402d030701c1203420210054030015014000010319454501b09072843e09001412441c10300080c0e0507440c0024400000b2181564480c0f00885600c10120b19804070032107031030308002c2208002250700981c412002507401e221700c1c42c031b07260016a00c80ca0028080c5900ca1806000703030307000c02001085407c0d1a036030400c041c6240740c0140040c0069440391460706540003510103d416810001e41082130540c100140ba800c10f01c110082c5c20b12a40744000600110b000d030310024080c40c10000064150356062003540c1e41c1d0420085c041c1640a48400010380303030f03481a40100e98a001d105004155100180b0940748502d9141d11854034240c60b01c00151540e4064800842c0d003803207600510400180e5145510444601c0e070200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 502039667 1250 502038417 502038451
    0x150b0a031413080c0111030406050402010806090709230d0311070b1227010e2113060810150201140901022b061a040503070f06021b010c0605 62
    0x1401e44111500c03030907a0316085020701c81c12502884070080000d40c043d9002d5078070b084d09507125014205802501000160110810042c4413241c0c0029119030710036602c144440d40d8190811599400903a54080058845801071205d2407900b03440003040b82d4241d0b03c81d040408042c002404900c0e2054044000446020083e504e01508000c1c0902400385080882c0c14806600340e01c110030000142110041c0320303c241c0d0035542100402c43d6442420800c070080c0119441005882ea83d0b5641030b05803e40a909031301810314103503000f000d5035a04c4800c494141083d526160040710088805841d01030341150007080001d461643d001c0d1120001111780002c1104250340c0081400c00e00014080d002036401000040140c052158000c504603400c0c0c003030502e007640f1222a40c0001e0806401030415420001e075140c0c400500040904101c40c03044040340e400b591160a0407c6024462080d2030160b03115a821010b591290ad154002c1c001c018076007141890141d80b82d40b03080d11000c1d18071405a00f00105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 502040917 1250 502039667 502039687
    0x30a020a1b05151305030703150b0a0b030a140a0c020307120504080a030806010e0406032109211101030b030a1203021c0506100e1e030709020f03150411040e0901150b 73
    0x2c00b10340101700840240114130302d141c450b10300408000140388049a503580e0705165541e1003000c3e5030050581140d8981e01da140440d00030000b000805002d903801004000043c9228180340160b07403a0441e15070156041040640c1c486031403d039040a4401840418040862a030904001006c6010300030f64403449036080c0000050301005505d05424021402d20f0010b0001c82d80021200d913110054019080e92030004050403541d980940d00400050303c8007109a011f4810781c00d0030a08600d00407040c4c2040c20030000010b404075140c410740560160018020380000c01e00c0100301c0c040c000d85506015140908a517020542d240410070030002d4140d4030000c4c0640c03800e010213824850b0903c2c0c101140c00f2101c0100060030106a40030048080c2c0710714040006e184c030240b007001c0040103000c4040d51921100481c410060704101c8031000071148402c8481c1e940d2505000e402507070786000d850306140c181000d051020b00c6000600099130741d900e4498060100080a00c0c040040c4400401c0740d80315a8908 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 502042167 1250 502040917 502040947
    0x3040b04140a20010e0a230a12020105030702030f210f010b0427050901020715051b0a0c050d080601020d0e031903020a050607090f050102030a020a1b0515 68
    0x9640300d90707036030046044000141c02c1c0e07501c0e42d8500c119030f440e2950100c10740004139071040c41c900786150000c20b0701e0703000a0303401d4800080c0c17100600c032841e00b504612130380414049011014410075011000700c819031009940a03c000b075170048aa48192032400b84515074140140e4806049406d00c0a402e43d202542d03802c1c00610107400840c905c00c280e5540d4580491410980118000c0c81d250040e0140e0b041c0e034194800e080a280c01d0b084c050140641d01d04207000038002d400103201030701e144100000e52000011184a001c0c802c044002c0e1500c0300e8155800c6108964210210100034004035140300c5010403010032804030f0902c0281c0d030340c1c0340900e0204002400e000f5040400014030807080c101c54515a0003103404011181070380c1c1c141c00040311500303040b8540720003480040c010b030045009220107258001416001c0d54030074541400300b1641d5000490b40c2e80300d85009a00180c0150a921002560103c83d205a90b0480072400c00311740e8a85000911180004018012080000400344c141050307030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 502043417 1250 502042167 502042193
    0x60123030117030c100b030c0a140a080316060903050f07060902010323011a04170c010f0903080d05060609040f24050108040f0813140109080111071502040b03040b04 73
    0x140020710308000107280244c0d175560039261020740c1c442e1100c003009800c2c0c40403c02075640f107900811021a41d0354554104050003060a500c0d03010b00200000414840030010403250b00c46908030540a2031030310f50f1904d10050400c2602101000010040e02890031044c00140c1502401402c00141c80c111504c0003500300c0f00040c112920714001d00b000403080b5000300c9a601e045408490000c070800100040305030041c421504aa1070b034030b0401c8684566100b0000d00b03134030260420b0301c07548141d48481c5400e4a800c28a44402410000e04005090407000b694201c29000b00c00507010500f0580404009070942c0d4203d284140d00507a280da040c650404001c080e00f68604500172a005880d0801c0c000901c01c00c00104052300720070040d0402820020b800044a14901006d0900c41025440c0c49004488401d104842da001990071074012030700741c1040c829500d80d95070b0701c90413600d8500c19a98800603a010a8032503501e01e030307081c4800070381c00c100b000003944204d01c980c0001d42d103454646000c0103c1240303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 502044667 1250 502043417 502043459
    0xf02190e1210091505090a1406160507030306170123040305071b08061005040c020106050a060e120a060212090c010f0c1b030302010e0111090f090601230301 69
    0x140c1d05100c03140c090301041c003a41c000d070b00c40c00100c2c0c03035010380c1000011440354450402d80765150208101e402031000c2191070340148918100030028103d0700005076101c009540f1000318180b034040514140d80a0002040c0b03e920909000c10807079034408103001074001c54411407081780d442d410351050401c2e0201c0c60074a10404140344815505040e2002030060003034001c014905002124903554800a1180f108002d003640802c8034035500c0c0c80210f0344e80740c0a162164074041d40c240760b502d1881c9401030080c2c070282d4a002d0403408045150140854222440c0c40302c164014014501d140c500311030070300c0444000c50041c0310140c1d4420103078100843c1d0102c014015409900f041261452981e4011032410400030f2504d4000d0140c81039041012000d02c400043c5007500b921144000300305a010f4002c0041543e003000208803d1041d40302c0024603100d18605560301407500d0304400100c0c901820803540060040c50b10480c41e00450800a88180e05030340b0390015982c0200c0100321295a020074000b4841c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 502045917 1250 502044667 502044679
    0x6011401030614060a0908010509010207230d18031a091507020c0906122506030603031b0c15020307060f140f1503030a1101061205100507030f02190e 66
    0x22514911100c143c1075110003c0c071900001420416441c1305018520151122800030442c1d0704200703451b58001d6000500c210342600041540e00c01d02500d036900b51031358032902c03405002c0c01d884800701102c0080c10000d0518020718400b0010012500a035800706254506290810349428030003040e0346021a15517180880c4a03c03441041025907000c107018000c14030503a44480c042d01c1da100058421547c1e01110900c51007a580b801c50000c604072405080c0400812410f001c0e103403555800c505035030150002401040305030124500003200845a1891a4000c00441c1001501c03996580041102d0b6042d4000580c030220320796040c01400e100348024001e0802080002c040c0348148800711203c01031403074800030b6004000880d080008101c100b0014030040c1070765910210f6510280c84000010b4400749150700e4864007003460414540092806a00100204010310242c103038100581801040e40003059181c10000d551100c40c0e00107032900840580c061900d607483c40c240107100b044c200c0007191243d6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 502047167 1250 502045917 502045919
    0x807080705030d051608070812040b0108010203060109030803180a050706020706021606051e030112060b030d0c02120a02150d0b04050709050f0607020d060203180c01090e1905010602060114010306 86
    0xa60404100c070201c5e00404a8010a1041414440d0080c003070f0341e001910002c400103c4880005820450520032031260700c2400559880300c50f85800c07404215001801705045030400c0c00400c18000141d40c1c045986006150300000e0300d0861805e014800070110b68540c003c24003409030603011f10124010740f8032440141840e614103075035090b20003c140308000501800103201d541b649030400400841030114450940d86e560341e1270303035002200350800b020b03200f051502103919200d00c0c02207181404401c0c0359440709c5d034003d01502006140c48003602c45103000c3c4a841d0320308005071140aa98162030701c244600c1900d0784913401e00c0c1002ea450b81c00e4001c0c41940340c00200b24190303400c0b4240e83c2c00e82c2c500f139070062000e540a1000c1141c40c86000e4002c0d43c04880720b5811410022182c0056103d2030f0355904c0e045809901101203070b501d89102d1100340c0071504032101404088c20030042258020200a58030b8808401c0c9088001107410a0304050016002903005000204150510a504400a00c0c0401880b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 502048417 1250 502047167 502047193
    0x150a0207180c230c0d020601150305160311040e04051c020c0a0326040b04090608070e06040c0504180e0607140304060b01020102071707050606010926010213080708070503 75
    0x50700d10700082515550b040381d43c00c0000c034a00181d8140c07541d00f004483d560304038404040d47d150424420700c480d8036801d00c02003c591f4481d001d03040c002c0c0852968181c003000078907415809005841c84000c62440180000150b0585000c100b0340118000c40c0a85505d80c8080501c0c1c03503042503103141d00103542c040c910f0350b04551070380090202200d4100700c00700d01c94055004000f110000050b00c1110050011501080c000f41c15402002160104407003086a10b41d0b80368015155015482803401c44500d8600145007410960440000f0000a00c0c0c4503150948441741000c298611480d09100281d881103c101d0003141005140c0e0880e51078248121195a4040c01100d00e100060005180640f243c0704584141d00035010340750fa041d0311490581c2a02100e4521003550f812102c0c05481c02d00c1101c010a4181d4051a06c0b60152110640c41c110507518001d00c8419006c00951070001540d800c001c0420041000e40074500607045032005400c80e82e03d4045568074256541c0c000f5031007a007100c0ca090541d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 502049667 1250 502048417 502048427
    0x305060a080322050a03030e031e121e0d050906070905330703050d110301030f0f23070e0c030f0f1003150b09090109030914150a0207180c 61
    0x240c0042c403c02c20412422024a107040846140e02068100900402c08420160498510301b0b00010035030845c1c28019903128103030f007540e4804d82c1c1d84049070407510046031031000000043c480d442e184034851012900102e5054032a600002c0001c01d5241d4400a224541c0340600429421007601d15001c0c070024200700008001148010100102040c00c13a203000c0f101d180c0071070701c042d207046462609459164038140900107600c07071500c4800d01803910501304c2d1441c9021064a068a400880c86035903000540d032850714082e01d183c016550000004100741c0d0030b0804000e40203009403c80003600ca500e00d8403250040000d00940340880c0c441341881040f00300703004141d100380d011007040607010454641c17a04801c40d000fa95080902100041030b504100d02c50141c00c848401101960555010390320b10008134202c4040090050000301004007c102140001c1d2101b1100301000340207009002035640d41610540c450f0140c03201503084694104030941181442d40751742c001d04002031104860440e00182 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 502050917 1250 502049667 502049677
    0x21c09030e03060712020717030405340306090312060f060e032406010504180504350c030c0304030b090106051504030816020414040b0a06030803060d02011e0f0305060a0803 76
    0x10406501140d10380a008805100704290b2000c481015903d08050801940301c07000c2810700c051101c05003006001c2c030323310300c040000c0c820210144030300402e041d030765407801a041302c48043d410401c46071203c142a90852180708001c209505561461a1a08802900503114502030034030a030000442e501c44080090343c1030000043d9000240310782d0ba03886006840c68040c81c0c02a040136039500d18065418020b80c1c2c0071134001d41c00b910b80404258500c152034a0b18402c0c2c8c0c03416007006001c24010925141c07880c4003410f000c59441081da030500340311b041c01c1c0b403840c0c0140d8019154181140f080c0f00d2560820320803240507003400c0d15010700070207815001c207240c2e1150b40300081a060000440407120310b44643c1d0600c026030300420620003003280b00440601000180c0302a102d442d52200401c11609062003180100c1c2d0344038801074116a03611042003e0100d01c0402641446020814105c4181518410300c40700d100c80c1e1101a504094114000c017100c000070180d40c000d00d085c080c180035030000041510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 502052167 1250 502050917 502050947
    0x2030319090b0f01050319051515030a1a0106230903160305010b09061f11070504051006021204032d02060c0a03020111071a0a021c09030e030607 64
    0x5100c611024214010300a039007002d0280d005020600219410344903403541260001c804580e01660700703140070540300075a42d0005280d03034000c0ca0f18609043c41c69800319400500303010001a500060310101e418404908011141d100204043c1d61039400c02604185c050718041c90000d07100c41090382e991620300ca514100c0c104040021030681c00c540c0c1c0400181c000441500401542c0f15542d14006000e0140300700c0b09440f4154480c001176a038107111500c0c21102501d148203c50312180a602aa001000c400c104a424000c00c0c40c0490651030b41c0c0070b264010342031400c0031040940340c541c00034145003008000d1414601c041100308040788002c00c0d00062040141c0102249004500201c5000140807038001c1d00005c0c08141d03c4480d400104103003503264041c0c0c009116501c4c101500000b184200c400041000800c000070f0140f40d014000340035030114003801d006140040598101070300c0b5200b051000642a100c4200703400b055404004006218070950042c212424024070140595000d21000c3c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 502053417 1250 502052167 502052191
    0x1112010e0102070627200d0c06020d140409021309180c0803040302090f07030e010c080709060315030b040201140d050103171908060604050d0812090708030403020d03030b2809020a020303 82
    0x206c40108040514145901e600414110020340d581c0741c80014019148a0080540160340d000c0b464107008085010072402e400415600d01401d0203a880000c1d0030408011041d002c2081c00403400c00800c0c400c6800c00c0750000010440490f00303180100a00c4881d41045506401c00d000420050f1540903449401080c5800018240d64825200314001c04d0301e9000c2940c0382d803c000c071240e5070075045180240034000c55a01c031800503481e86416800d42e40c44000346046030f0194581040481c0320102e103140c0140c4145001d114100c125031100300ca82d0491050504019562001041007100c40310002c016002c03449425401d0102070a01e031103200003009010001d00506c44002415aa21142150054a4004c02c4890107006074208000c450300440340703507442a802c0c1400300380b038620000740791030441e04d45074015071401e400c40e4280b200040540200714203041d00ca603004e0b509540c500151280c021003c170f4010f825280708400e0b80b024114280c4c40f900385503104100d001e419981c04002c0366808040340c0c3e50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 502054667 1250 502053417 502053443
    0x909032502012f010b0307120f06060b0318150c03060904080d060e090d020111040b090103020f03070f0f05090d17220f0b1201031112010e0102070627 66
    0x68582082da5541d1007404494600121045207500c83c03103e00507002c403402007140c001040203150362144036005580081040580500000f0000c4d513888509034841e03100451407940d0351003000c203507400690b48404d055094150003407145104202012440d10f0310000c21503203007804811040b43c1d200280c122406440d44100160900190760102d07030702c1c4a482c0c481042400d0351104602110042991400118012985203842c610f105003c1c090354501d0031820546094a0b214422125600481001c0e06064003032040b2007003101c00b90701840c803c0321941c40340708030824103480c010445a046504d01062200a200d0031170f5031348030700f00c502040951180c8607239400020000c004000d40550790b0b482140306611084a945800000464000c4038101e6103680d01c2d00c0e8451500c0b0b4054010001000c100a0840c40100041b0712121720141d03030000b000d0304d0a59a5000d02c0196800d40f44005907250643e0340014011007002000d02c00c1801101d08009041010740064814848401103840b000c0c4c040a26180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 502055917 1250 502054667 502054669
    0x60f040902031903180b0f0a0e0a060809010b01090f090e0109052b0305010803090603041a04052a1c03050d05010816060f08060411070515060909032502 67
    0x1000303246107a00201202c22114801031405800306505a003240041c40c00b00440385070394a03040000003070750300103241c85040801090745442250002c07100700d0100f28014420000d00c0c0c440c00c080b00041c24040e690b0741010304e020309a003403d44e00c60180d6241004010b00e01009a44104d4a0000c103440d1400307408101c41c404411014058480c541c405400ea00900b0345203280d904a400d8080030122280083c242e0707041500005030100c49003482800b0454101300400c8030949450740c01158418401c0040b802d100f88030761152214110200d50032100c80d80000d0806281c10100c0401b1301400300415441840e20f1310031404074250030341d00807e02d03446032242c1002004050040041e03503a10202140b00300714941c2d5a405803942d85480d4510a81000d1b000200894039510907601d45003400d42a07114620a0f846250030302c002444248080985900f0a11034100058028880100600740e03603880f0001904254040104c0751701c015050000981c001c00071915400340e02e5000d040041c4041402c0c0c001c1c014980 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 502057167 1250 502055917 502055921
    0x109060e15120403020c060a0815061612140a0c20060a0306140a05010c0308100812040f0e060306011205011409030310090513150605030109031e030204030b060f04 72
    0x2400d4035101c001c9040d0b10350319011844584603500a40c00c881c2803e1031170b010b000d400d100b600200030002e0031840c0010440c4580055030140d07100041c050a103400804141d44e140410200c40071585e0344498030900c44400e5000601c45041c89200f240f691400c2c000c01e5010703010381c408802c010722808100038000c50038100d6001d03074044503034040c00003551803200040050040856008404940230359080384070f013901b0000e04600c04d903401a162034016103501d0300c1c00ea0742c6070801000c4110540e040400449c000c50240012a150082a082a6222810b1400c125042240c40d002105415226403c010140d94000341c006d045540e41d0403000300302242400c0c0365016102c14203c141e18252000180140000c00000441c403071515540d094113010b0700d82c00d04006070b03501901c00c2640350f184411510003155100b1084414002c0e0040300080c03480c1e0300d030003090075144502400e5004c14000303681d00d481d4044018610b0305907003044c981149030030b0071580d40306500c0f40041c21250007002c0e980c9210165450359 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 502058417 1250 502057167 502057189
    0x6091e010204170307030f1e051606020a091a1e0c0118150e06090601090b030f01050408040f080d0207030f03030b04060b0c16120206030714070c03110f0109060e 71
    0x412a51204418415640395aa40064800c800040046030400c10740c5104d10b030a0010700c200c82090f240b0201c40b04404407507a130401c207070300e208ac400010a1840090114401400c00383c0300754440391021464581c036a00d220f4180200e043c04001c00f004134a903a1109001038018413030000040c280c468109412132401803414a107824480c5520760b2045050000c1d41d45413118807034880c803040c0100c0112840c801d480b500c00340c40d543e02c2d91740040d006109141c01604440511300c800790444942078480240d207030945500383c40a41d280d50000034288112030389162940c0c060010f04004140258407020300075522000342c4030140c00d25100039507030b80c00c05101e5004200e0b80103006006025240d01c0d41c60501042d40300c444054500e10907491035180840210039030004540e14515071000101c059000d1000d141d1004095408000441100c007140d840340780054820540160758800d6114158900180100d00701c000b000d12600400a08480a81e800010710b02510110b1606c03022103001c4402044410b042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 502059667 1250 502058417 502058429
    0x4050601082a0415032a08010216081804050f25080105061c1506020f0708030d09170a05031014060318070b0f12100b190903060507020f0105010806091e010204 70
    0x1e003038240c0c4d0010b0f0b01d4400700c85222200c106c0100c1d100c0d07680301c00500b00d11841040c400c000302017071941070210344048080e0414044007c0031015441c0c3d8600014119079086448400551200e4244491121380c1100d4800030300c07450010031502811214080c09502051250500c0780d500025000841c50401e403951090052885090041c40040f03218580300b14002e001c3d0400501c00c02e102040d2510700020900c04862a0f1409503113407401082100c2d01412042506480000031005854001082e520040500c00c0703e0350390329503d81c10495a00a92400030740c0c001d1700041200000d100d002e80c1e450013220b40004000d000c0c0c4040900b030b00021400e200701c80d032002c8074402002c07400301002200c800042c40c0180019040e001107030b89000e0440041c14032030003101b180420074403101c00242d28159003035180d9456030400c68100390740d1317030360b810140c1c2c004403240b01c016007100c4100380740d8003170074013601d0302411203140640350710f250142c01c2a40e0f402001581c0d0540703105c1001101d440e200298111809084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 502060917 1250 502059667 502059683
    0x10c020a06030e0606100f030902040b1522150e030a021c21020601030f05030409021303021e0622030b0109021b01111603050d0504050601082a041503 66
    0x181d9400c0203001880110700340803260180d100020b00d94588440e0841080c90207803140580d460004034100d00400e19440105d070003a966030580c1c19542c0e104110403805a410150203036580d0051305480001c0b000c1e0b42c00d1101000b2402006000c014165040101c1d80892407610788040107111001914008082c3e00194001390009000002454090f900181301802613107020315007440001d00d80031008904144c5801600031400510000300118406c10302c0d43d0183c2c0440e401c15468258200c22a4402d50156a000c110a0401c10441c105880d07524019407000907841c107080700250100e4803910421040d01c1c4507045042007600c03e42041100c08025641140d28030900d981c4981c1c041c030080d804900381001b908036440b4404a80b41050081340c0116501e90151428000441042e089581004404400b808028800e4080a4441d4468188521300620081086525040407503040c106c0c42090510541010141d198003a01c14180c406040e000a0301c00003401e020500c42c0c50a00c9402d80c0000709116 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 502062167 1250 502060917 502060919
    0x7030302091801080d110a021207080105100510081515070503031806011e060f1403090a020f100801030f0201031107060204091b1215080a03080f010605120c030402010c020a 76
    0x1440c2c0d8208907060310940310072504040c00c0300b2070555200903044090003c42d40107600910060a00d4031990703880408180c1180d404d036840340d5800c1e0940f002160240307120701c81918104443e1400500f0303085101c1c2c0302d0402c2910340c10502c0c0100e1032009109407060081e0603a04113a048000c0120888031182d4101090f240c603400c2410402119404655800c0c2c0980320b00400407a40140f1015002955032442c1c136041c0e500c61902c1003e940103010503454905020340820069000004003009501ca020600c0141100d81c2d05881000034403c0020182e1340070b000c842501103442c1d0780040480381034a030806120110588544012405040061507120041101061a44c208509900a80141ca104c00b105004850400c00a29810381c0018241c2000500512030b803028600c4a50002032111400b0081880c01515200710b146000e10038503048000a000208001030075064003c054051720a524000d860403002010259042d0b038060484080e05c540040410116030050715400c05165000d40200c41d1a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 502063417 1250 502062167 502062199
    0x50307030303140c0306100305130c060509010207062c03010b101709060c09040f11030903070c051e1002010b1809012016051603051e210703030209 65
    0x2030030046000d03c51022071400032903001000e01050328030070480a40380d002c005c2942103003100036110107840560180341060742200030a003000c80d40c0d409000940c40d04d5a480d06050002880c02c480b5074094000c1010502860030200c240d09140081610380c81840b460035840c0200190041056002166100b00c4040890000c280c1100d02402160b0710308480c003103035903a00f4010035103c650441c5e098552a204018100e102d01d400e80c40901241600c0100041d0201c0d2518105503650041e200b00c0b140364000b140480401c80369101c0c8002034081035484a1000304002d03220028400c102c078005100300d1f920340d5240100351003588811032800004010103e1075910540c10030011a040c0d81c012015400d2490b02100b280101b1505002d40c066610a10302d480c41102c1803412550007070000703d0b55400f03290140541d076641c884d1850007541c0a08040c1040d04d41742c05000080300100d0040344800c0e040183c03640b1400c500305032a0422200a2040f06684801601c0c00310028440c020000c0e50242c0010915501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 502064667 1250 502063417 502063421
    0x6050609071d131b0f17010501090e0408090a030302061503120706020c03190c02040f0510150c060e010209011e140913020c0f0601050a180b06070506070c050c100807030c09050307030303 82
    0x8200d01075102e11b41614074920f0541000542402941c0c0402c0c8901c03001c0040c41030300c1ea0038a5000303019070328040c241a484d400017110f031104c6500c140d00681c040828403d00c0599411101c000d00c030214000c0941030614100b20b4014000c82e0000782c002e41d40070551400c0c02c00180203d80035045611001343c50711903001406001020f1250059008a2400248046001c003a100e41c0d8050a00b120f07101c0e42c400c0c81c02540313002e0003810307820031000c0000810180000611901801108404100c005615507003024001040070f5000211391003100e003031041c071521094006e40c1d0b15840780d610880055480d030f401808107102d041c84103401882c40784009060301041101080d1980e9900100f0309985e1180d80c0e0f1010050141700300c0c0240581c1d40c0d89061400c6254050b03500c54503543c00c01800300323810701403581c50310760905404031031400c003080640b160f03c0100082032104108144088406000d0440c021100a01e990b2008000d9400d1540d05c003015121940034100c0705000f031800a0440e00e500d5281c1c070300140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 502065917 1250 502064667 502064687
    0x4050a06030c0824060f0d020f03031c0b03070e0a0f180305070317150405060312220905190c171608011502060c0304030e0d06050609071d131b 63
    0xa4101440e01c0190251004d40002c1c1c0c003402c40205108186191003003000818030410a040f031303101d8044441c262040c2c405001415102034072041c040c1240600c1e9440c1001c3d0b9100741d03c1da5102c1e802441083c0000c030b50540c7d900342c200d46184c030f0014010340c08124580090232580115550807071000c0d070600070141e2100c0200b2801d071182e511201c051440b03104607051100d0a82d4401c00c400c00e1460b00d1200e81c01c1c81d43c4041e60014005080b902c1503020201005c041d5881a410b5100c4030802e8845010f410080b50407000042541c1c480c00c101d81e107086001401c103000c441006004e000e8403085208201e502c2120305203c001400e5140c0c07502814100c0740198985404841c3c8004516400000608280b8803009451034614540103405d49a0342c00701e42c095142d10050003201485001302212080d43c4560740c400055611403440051141007440420038003030401000102040f52900341040d00501c0f4540810100d00f050701d603042c0391007000c0c500324064500072480301c500c0b00300e000080281544c8081d5210b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 502067167 1250 502065917 502065943
    0x60f0219030506010f032f091e01080a0c022b090b040e010311030a060e0604030306090504150b150310030317090705010f05120709052d04050a06030c08 67
    0x44058503620641c160382048401d60b000c0f40a00c1012518140240c00c699482c0000460a05402d8094000c80310785010840e07641c0070442c8040390b03581040c148013002d0800c0300241880e00e0380043c1b004c0002041000c000340009a80d9486800c22811030740200060582c1240640c0076007924503100305c10070502c0c4000104400000c41d0b81e40001540c18440c0d0486054569a444000180c0c4c29070325aa5503c0440d032101d150180300f00041b080100d09a0f104e8004000b050740080c000900701801d00505440c800e410400c030303051400040c03000207010710814141c01c2c03810384c20200d500e441c0c0c10001240520030009610305004001308204c2500740b00381002d4103807446516003000d51030711443c0e034400c004c100f1501e91030300b548000800d008540c02103081780989c104500e000d520300046543c940e224140c0a070740320300215528990600191600200100406181c02440d1100d1500040f4144038071907203009060003a5030721004140c0040803070700054099504041c0d803201540da2004c00700e82d15031070340080b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 502068417 1250 502067167 502067197
    0x703091805060a0b1e2a01060609060509130506041118030f19060b150c0c030105091b04090f050d0f020d09031a09150a060501020c0d0302120d0207060f02 68
    0x4c61440401c07800d9500ca001020328a14500359a4503500c04964031405000912100c042c1e401c0802031116080342013500303d600008108249003c501401c001100c0d002002441b50074001c01c1c107581c58441140410f079810502c04544da0301c507a00414010195441c8500901e034002686201341c1c4802ca061590300c1105500b1100c180044550580d1180b402c01120101c0180401c1d0760004610702d9000840700a00003401d0a58295000e00700b0450781e031002c0c0c5039001e02c0d00314041c0307041c00385400e228840d484802800540141e168804c3c00d03450039418980e8440c451583e0b00035a03401d01112851510b00c1c260701c54120703842601c80c44809028000e0000449006100300300c00e401c1c40900c0354007070704104d95000300c540c40e1013034103e6100001e129000306811014400e180c103442103040340030401806051151000204541001c000a0500e040c1b030204c1801030506200007000264001540825403038103401090300c4d0015004940064850803501800301ca041c0080040c507180240d0043c0322400b00b00c0c0607 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 502069667 1250 502068417 502068419
    0x4180302070f05060f0a0302090d0605010303110708031b010f0c02031e040815190c09080d050f03130c0803070c0512060f04030f020a020306040b060301050c12010303050703091805060a 81
    0x3120000d20340310f000e01c580200040c80329075000c20a07140602001c81950502504101031180801e0101181400c1030740c1c0c2a4542e0010004e00d03802c1040d200f094403442c4003a1060354201190103581e4890b4442c0d05040d04051003000904134020751003068a05540c113000d010204016200964a070000140d0031007800c440c1c6002c0c40848810401c98007100c071900040e00d001c9145007900180a58018039100c44100c81041e2002c0d00e4030341c0e1288070080b180c1c0384c88400c01c1d581040e40c01032030810000700003c244002000f49040e007081d0780b820b45c0d501c070322494209000d400e0a1314021407900260340c4140d040d1320004c5032110400007816500d40039103206031210010003445955059441c0c8041e90400c0420000d0b0001c940424424444a180c43c40f660040303418441c4654042494804111404d45845440805001503480d00b0f01505030803850756500c0e00c0c20010794180041c0c0701c5506220050600c1400101e020805016814140041c01441144a013000417006000e026000c1110311611601030020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 502070917 1250 502069667 502069679
    0x1091b1505041514040e09070807120b0103020f060403020604140f0a051c06110406170a090314030402150a0c060b0102010e0a170f0a0c03020c0109140108150418030207 74
    0x1c2981e088070100c40219682c0c0d00045001d403240302069810b5004500c0070400400c000c10a55182802042050000c003402482c280c034040c1003c0301900410325512a020011010501104942c1d064940413100211041540702c0020300d24402c5500081d0030002c041400660203c1d106400300e00e028003034515145002d000f10802202041c1801801d0384080441c4a01105a40034040c0f040014420000010307612011003090311a90000c3e488a0300044c01e1540c4004000614038141d5009030b1074070f00c1800002c40594001c2c00110000700c0026201001000080a550b60320b6100781341100c24004407940c502d846e0200030100e00707100d5403d0340c0040c2004e406400315481446206c0a070900e650250040700c41e01d54483d82c1c050440381081009a00501c100000040154000c120710b4855481d03940352120321b441c0280c24114140d0840d410b102c4002000c1180c200d03aa071060407924024600300b003440c0e40e48268010208070307560910303420a240c08079105400700e4aa00613a042400303034080f602c81c503075919 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 502072167 1250 502070917 502070927
    0x105150f0405120609012f13051e0117061008040510020d0b211002090d1707200a0303050307110a0308060102160f032411190f020a031101091b15 64
    0x20003800c180c418034000c0041f0760f075070000a00200c020301c000b201c1070241e81c3e40004d207002004d0003084550b149940340144c1c1039a0810404522501e503010f40c1102c034946440051000700b00540c81d501882414000074040000601031540c0400304400115164140d0583c020000c0c90110300141c055110354440c1c204d0407a1b164a040074081c8e442008011111510b075201c00a90010b865490b000754225981d80005580964100d034051030104165450f0301041c20103060403110300e424240c00c288403a0791038500751500164203043c4c0e505814500d60b26180e121003121640c40118070594140601e00a40c000c1560062102d80200400d07400c8410103c0c1d9050441c40205071340c450451203580e10f103030800000310174030800414843c41104012100c11402140403d0310703000e5150010f825400180107641c00440f410303048007011285015210f5041058010755180c2c0803d0740541401030841c96a1944442504002c1d8000d6015980c08500c0d05000702801060626004031003a0704c02c1d044041c81907910a03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 502073417 1250 502072167 502072211
    0x703110105250e04051e070c030c0f020d0812070e18011a0708040b0309150415091103010f050405010605030a020d2004090317010803030105150f040512060901 70
    0x1800355020b005008040c01000108908181000d1045a1488030761680c0e540c81800e11410f1003000041840314001d207400c8045c1801804d55051055042e800c8010035403003120240d0301c542c00600c559981c0c0803400062145042000c00400c07030ba0b400120f04003504640c90001b0302a802640711140340d100c80758204544040c10f0410385d4016510f40004001040440ca10258809480c01e03440d403a00c1d1180c0c0b42c00300d2580c41030f040504100400800c7c004c60b01001c0210080a40780843c101c0c040782003581d00c18106402c90050158000e4490002c03000f032201c0040403a192000080080050418511003000900340c1181d041c2c881d0751070b00d1070000d45801c01094070510700ba802020344400b40e1459031048044291925034a9600c0365601c010b0525807958801d580e0058080e0326070170052200070201e45010744050f0814022070f04240010826503c9022500b9810000f1b1598140c82d030220341d80103c002d014076401250b0200e0305020b1600003400101d00f460048800100a00200d28a20320724000d0641e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 502074667 1250 502073417 502073431
    0x3100605030a020405150406060f0e04091113061e030b130b010e0a0b0d0b0f101505090d0c0303030b18011a0a0e15030a06171507140309030703110105 66
    0x1102e280c42c001480c0980c0081d5010010403c007403240910080440c044581d1a04080d010443c408400e885807078110441d25802641140d0030b10078050150740d41210a0005214507004040102c11101c060200350130140107040710728615141041001440c4440d04060f1100f524200d184501223030421942c0e204201a4940040d400d02e01a468040e548525400061142520039036484070a40d860b640d0400901c0c103140150086070040c01c2c50303000a0300c1828040e1100140a80283c41006203a07945800d41502c0304650030819100d210360800b0401506801c01c0061003100000d10101c00c05815a210481e400b20994160052001c182c0c8480c45040c0c0178010365101a401ca04030001d0410284010074100e42c5918182060091040100c0c03014285500074811141c0d0210070440c00c1340141c8500300003801351b401d45030308604402440e07540301c00401141c020b0054404e4000783c8080d001c3d443e0340002d81500c1814642d2490b0060401ea02e9402140d0200c00040501d406e070280454140103039802105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 502075917 1250 502074667 502074673
    0x30f0306090b090c03070507050f0d0807030c020c1c050105250504030c260307060b121b09041704080318040225060f0e03030103020a0803070803011502031308010b0310060503 77
    0x1303658103011102d0700000c0440007000800c10580700000c0d07062010070140824880106000c0e501000f01924080d0028600400c051822088041da16030000c1d400080c00400c0d220b0440310002c007000840c0120001030003034071541c00c1c801031000050b0f000400860b155040d404800c4c0100700d54408a901b44503510010701802d0184000380201740c0c030018140020070b001440180c06500e240d11280c11908104001d45401c0e6403042c0c0100241040b1010075078030700c4800081e00c01c1c4102c50030300c51071204040781303a28021502c81d400502084509020200b002c400b5140694407641c0d22060269254403d0b880b00035442c18078114000c9a0a181c02a10341030b1800070111520315840d4150044071000690094628580750124080060107502c07402ca168265880a140d4a6046005100d80a440f0780c3c4030b120540c1c800c10000c4003260400c800d40e03041d40c0080c0c4404401082c0072508030b1450140c00d003078689100d028000051004815400785264000c1a0180d50154210004190450300d0398822036030550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 502077167 1250 502075917 502075921
    0x1c0e090604150b1312080a1d060409050c0c0703050f010614010f0c020f0603011418070f1112040b0d0509011b23030c130b090d0627030f0306090b09 65
    0xc100034040d20000c09507082d51000165a000041101045c241084e00c46420004403c2d03540b9500018000a00b101e00b031003810116805000b203800c3d48510701c100281543c2e910041840d48501c0411032701c0300381c081c200700c0340140e4490038034a1300c451490101340c40769803a00500280e0344088003000490820161260b120080342104141c0f503014081d10100e030b0101000d440142203a9600002c3c5002c1c15030001e2441c1d24842c40c1c414429040084001580c40e21a02c4080110b510b42c03207008981c0e1031666251000c8100f1140c07258030300c0d0181081d00441c0c05440400e01103102100c04018180b107a049200c240004d0302c038041c9081c00c0320155242d1055025030380f110754001e58060120345000c030070a03214500352200703c8070040c4416081a160031075031081c00140002181d207000c0c100e50181c990b096149140c4441403000a2140d003d5410040c0303443d4503880c041010840031840041c40c2120800e203107036550034a140044c2407107035501d04170000c203207010004a2000c01c148502141a0b40207445482c2d95 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 502078417 1250 502077167 502077179
    0x180504030806090712060e0a0b03030c0c010c150c0e040b0d170a0917010b0f010212030406050c0c01090515130506010e09070815011508061807021c0e09060415 70
    0x103e003005040000f40154800524162200740c0300306002041260030404103400c110b0400002d0302c099050591190740248521440300401181d118104102420078000c80c01c480d190511400e415010044880741c900208030440e240c20422400d262001140d0401034031a0404c2000083c90700380d100585203403012001d22030b04c0c011038401031691040724208032900e1941c4060b5400050041c0f04401c5150351140c841d10344a0900c032040d4012490b090000d400e91404000c1c0084443c00010800f602e403e44400c0450940d140c10b000300d410908022000303000050050401542d5090700e154860010300c0075000007012200040c10b140c0302e49601c04090700c81a4a041c513441c05403070001e05445414062103400003400201008003849a651546852000d0341c03403c600002e080d03003098550001d03c001141000056542d2a0395080024800d1201c40d9a603110068100c1c40d001c18410702aa401c00c40701d108100550300a4051644105d049a10007010780e5004180300030781d0a086003550304503004403010301c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 502079667 1250 502078417 502078429
    0xb01030f020c150a0209100c0b01090b010804080f040509040f202d06071209050a030f030809012405090603030a02070608180a0303020307020118080f090409060e0601180504030806 79
    0x4007840c2c000c01740c1061125000a01c0603031314504e5420118501c04015020040e02c518940d0051042020410401000c54006002800010b10040601400090b07050402c8142400c2d5405000e001d01041b00600d03040c503001419500c1604159004450b044100c0c0e1801c8201c08445d06003403016142411800100095106142a00c802009200042e50b4620310340c5d02c4100242980c5409444d60400e4024405406414006180c00207801070b0010a400d00c08940700401d580c400540c10319001089940c4c40d0710481c01042220b41c01d40600b102580050004518031b1440000d8590480340c403400d54481404141c0e42e4403030001000091703000311000b0480b46010300461030f0301821107a1421604008603100900f4100364200840200764040180414140c2c244a804044600020701d50304120803500e8a0015014003024004410000981c210094842d034101c03588696001a051000851030131011b41c5414090040041d54a04400d460100c025180640e0b402039405032501d0303900c0d44a840501c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 502080917 1250 502079667 502079671
    0x40b090a080a080319060518070e04110a021009021318050312010f270c1b0503030f0c0f04060e0607080d051b07030203160302150a0b01030f020c15 65
    0xd8000a45a00014192030501050142d148181c071182c2e52880c01d00c40500d509450407800c807181d00c1c5408018003281d201e0039500b80440c0d41c1041034803540d03580c0c1c05003115170f0602c4074550341e00241400404240c41c3c080c400500610440c6400751101c44031028a04003c0340e00701c580c040d501400411410201d009140e1046030204941030001700c0032411030315002e1455011160a109440106004011894850726030f4000f4252102c48210718510080b1034412046d00ca1861000055480c046a150343e4000c4601c2c01e1031030030034800249403401c00e0900743d4694004440d0001c02d0403443c00003a0380100150211905400700301a40c80c241410f064003103952030000d401c480d070040c804100883c0410000c070041c050213000d140b0089940e261022840c00000f80f0b00c4104241c00206100c1140040e0300030040e02d41010402c40203408140b6039003000c81c43e01c0c0c111040b1100d4040e06800740440108181c0103082030110a0300d0070f00004800c840502c0491141e43e88181c601d0f042030305070656184400c404a5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 502082167 1250 502080917 502080919
    0x1180f03020f07030309030b010e070c0b100f03032601060c03030b04090f080d06050f01050702040e03042d29030a090203030d0b0f100818030f0a0f020f070308040b09 73
    0x79054a60050b005460000a50025000304001060401c200300c0350020240c01f40209600b0f090b00c5080c10b4030080e0008000e568001d00740128040042c42040c04900070400402c4403d0140c48100d0342c030304001c0c010710802000d02c86400c0c001e2440461110548001da4100c48281e501d1240b1190300351011001071076942102c580c0a602d03800b0000128881d0020b120920b4000e864041c6d5a503000b07095007046a460b40d1007139018103400140b540032a17070441c042e00d04290701503034085401341c500c088107400d40c801c941001503a00c110380b0120341020811405654228011a2403c0b041621107203c81c1c1050080c01c02c1c43c605050144900001145034000f131a00000110f44c08110301b03031035038000380c2590081140e000700d0343c1d6907280000461034003100c1107103004030a8030100c07190460084000c241c001c0040c1352446040181c6030440160f04c0410448aa02291400d66512a111510001d1001040b180b540c0014401c2c006584c031074600128240c000c44c1d5004907070600c0e01385071508103503141c0c002038441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 502083417 1250 502082167 502082173
    0x3011701020f13150311030c1317070302010f11030a110c0a0801050720030f0a020319030b42090a0803250b1902071a01061101180f0302 60
    0x1d0002c88007110080c040c0c110001051246150508112226a0b807596031080c0404d4108020035001044100c100c0c3d41207455400d841da613680e101070020540a58603030088800e0040941c0314038880001044100990b80300b43d90381d290b5035400040c22515803188226222040d003081021400c070500422041c0402d944c00e109842d04d0700420030010351030f0300003641304407d90b945400410021550007494031120b907a16070002c0e01244038070506183d0f80e0081085031a198600012450511802003050301e040703520900c41405050010349005019285c01c0700040d011701c807102441c00d94104204a4080207035020064008a4130021895500502e003286040d9400f0404101000301503e9004224016141d140001d640c0c685032101c031410388220000c040000198045100b900107a003489610390803803c0301444c82c02c1d42070405030081c000c0c4108a8020419101d810705100c40c40c0c600408281240c420340c4421f00b03045d41504c103039130a0f1101086a03110f62060040100c4c00501044901000c00c0c1c00381c411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 502084667 1250 502083417 502083427
    0x3021c14070c0602010606020304060516020f0916030b0607081608090301090813060309020919020409020301030f060f0c14031305061306180b1302130c050a0201200301170102 77
    0x80003650701104050741d0412010b81c0c103008150b024018200184090f200940c5081c0c90f00c80c00800030300620400940d1740c514200d00da41503540b07100400004400003000001581400707140210b4a842c1010a400400d050902042240c174000c0706807040203401646941c0b074541121182d104900ca0030000301d8860b8000e100651050700d09200e2003441600ca40703441035a40101400c811103288295004100f003605080c1c0c3c140058464841c81600b08550b51740304803954035891041c1000c2e0003180c0100c84410b101000000a00002e1544002d40c140036900420001400e035070303844290340160944001043c0707005500d03203c0162a2005551021154074000c0c954045035a03080c2c10180190303a8211050004a000e10900803103204c0c01000b141c00c6003168080950382d07600c00010b08401402d161b45020700145107001e40d01c946948054400b9140c2c4100b0000c07c0c0d035a4080d0403a00180510301c015032900840d5660b004c00010f40c1600b0040c80840380d030a682c078202440260180c0b2122100f80c3d9502804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 502085917 1250 502084667 502084697
    0x40203090a0b1501171e090109151a09160c02420a021002210403020303070306090204081b03030412210e0f060903070810200703021c 59
    0x3500380c0101e42c00d4162030a03c1d5540c50004086200690a40c1c90600034a0140840305004d03a203940c0b40c030264008029180e6031000c881c0b07070040484030030103004c2c240c080326078000e8510a03503c101c030f060341144219035440c0f80750780911080c20b2040b00e60220595000607800512802142881417962001b400300315503012601d031104180d450b0300040b01c0c40303d100b005d504c456184441c0c91320160084941401d4180640a8002503403852004550131000341d00285440c5442d20400c0984078140055283c01060b00707103494020342d40d500845038400041d243c00e0380441c088429008036006c4561400042900401101c98010300c041801345450740361200b0480000c80f40b112200c0c180b01140124034205600e00301c00e8a2154400c00480c05408000403035440b55517036074820f01801500794050314100e8941c603584010920b800402d4002900c3c1d44200f4090054841881d00200082001030140c200d4025440301c5140c00e41c05000782c02409600302008650a0a820400319101188035203008400080e80d02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 502087167 1250 502085917 502085933
    0x906030b2e020f1b0409020f0301050f07090807050d02041a03070801140f09060f100807080109060c020c03030f0306040b13050a060608090a080c010b04020310030512031005040203090a 81
    0x40c0d0365030050440100c0a24019010b00425110b1042280a07000c1d03041c00c9840c00c00c0030807130f0401185c481c60341d5903c10825500c0c1c20300d01d04020000a0001c01070b906000000d0340709075404660200000d00240380c04038401c10007158081c110741014003094900e1000707070700308006010020010916101c84003404590b580c0e042000c0d40080004600000b00c290380520740c020321840080002210003800000e10169000014405e6445140e86021b01c58035207460f0007004c0307042c03801d078841c00242c41030900205403a0010342c0880c0071356100d0074080250b48840b602c2070341c039801c0e8814801c0d030540040c00020310b003462802c015980064014030000d007842c44e5400142c1c038030500c20462000e84e5900c2c000c02214840b07922605010701100e082812003850120b445541d1121840d00c0200251808510200e40400940101020b608024001c1d516407500c0e032406101310806201c252514810341280008440040084a0085203982c40c0c00d200a42020b050101030340c030240000d0598440c030b407105008200c0c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 502088417 1250 502087167 502087219
    0x204020a0809100207080928060e010801080a0c050d0f17070201081003052a031c02120a090b0a0203210901060506090f0907090308030a06180203070906030b 69
    0xd9216a040c82c20030700e001510b4540714001d050a098410818900810b40000c1540d00c1007508644a00c03003400d05000c3d402c840d121680441b03184410380380e40420900c1e00b0003d4001e20701c8080e44c40b040c3d9a070760303020b440340d542c160700a0240419560440034001414450104040c244c0100540d91011a8a5503003003844070010300b0900f60503602040400c11981c2c000422500039200359581c45005041d911515256035140040801c600c1d421149001e0031450840a2007400c04000d041e58902d98248201100800a1f048688018090703000444030104450080c2c2e070301c0134403c0c0c1d25410250305101e0311091503809155282c0079440184000440c2e4403a6001618007038101520301803440c01c0c1803081c03e00b034900300d411a51003070700709000ca8080303a200c0c11843c1d2689801120306080740d40b10800107495088140e04042c02900000007040007111058000c1030465001c210480c00e001c655000c06400c900080e00d07007400203508082d003084601c0c0320f900034111640005041d10410049203e1a05004000b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 502089667 1250 502088417 502088437
    0x12050f070b15030c0a181104080106030201020c19060503180f1f02070312021605190219210503090607060f0e0703020a03170d09030810051207061b020402 68
    0x250703404202a400030000c4640469406400a1000c800007000003041c48103d4010359007511801301e0b626090328180e410a240805c01c400f0310036030351500d07140303a107001c0d00d00c2d40800d03409171154590281590810380c14118003030340704822500c0780728105072044490380d03c0a4000c3c0b0340413800151001c920102804450b0090705010002c003071040d80e414034010180750200c2c0c00d80241e413041c40060003103a00410f50300d2100700c40010059035401d4481c004d00140b08000c4000d0128410754090514400305003184071020390086034041404000c591840344d91494038050344542e01c031103071450341c40ca400035600d1801291141c0c003641c0c2001c04140120b038094020b09801e44070aa16030503c0c5200448910410014414007000f80000c42c2c11a004111944200e100c01019091b401200541c041c203804c05440c0b040100302030901501500d0300300109030100944200c6081c107144d210000d1145400c8503c803642c100400003819015192000a4441510960008409081c0050341d90010303911807005103c050030f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 502090917 1250 502089667 502089683
    0x305100f1e1d01060b1c06150207090624211112090714010c0804051c0203010506012c040b0d050f06090109050304030602030712050f01081207020a0312050f07 70
    0x9912101d502801d008444590b180303900d46a000d0040325510400c0b00c080c4611020b03200001c1d40d810000200070003403540090200644045409500c50b4045a04c0c01212000501806420b4403040f1141c40245400040a80003003400384295049000b02100228a030001c071002440342003500441055809140c905454500c0000300705402801d59009690040100e0005283d01414640c50803004e1040700e0005041c030110b08042c0c1e040109020840f4050140600489415070342c40c11407d10095002c04200c0c8a54200b070000f441c81c2d40b140c04008140000190100a11050a1070104040c2c4600f44465001619071084429a817920f000b002ca80324460b200901e800061201281d0030310764003800107200c5034102003045001c19000800d8902b0b4a03044000142d40341c460040c01e40d1911105a040d41580e814082084021a80c000209040715000b009640c003644d01600840a544188500258802494442440803450748100300b1080303462401c0c0303140313084003034890b601d515040300c40100c41c446 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 502092167 1250 502090917 502090931
    0x507150e0a23010504050a0305032802090a0905060306040303020306060f030103080a0207080d020309091012030c030e0109030b130303060302030f010b0a0b0301050105030a0e010605120c0f0a0305100f1e 89
    0x8640b0550035120300e04904000c110a00b05980c0d590b40326103881c10094104203010021462424140031003042500900e030046d05a0340740d880c3d02502a41001b001588604000100000c50b50050301840703114220003400b6207095591560154000c4d00080c101c0d54115501313004002c3e1680410005502179030160b8135a9403a0304c0580d000074549107082e00980700d1a04061080c1c0c0c0425000019500d24410440b800c00030b03540d45982c02c0b810400198820074204a0708501d100c185030f04014031344242c6003c0c1c0d5400341c280300800c0041d224415540710042c48120024000b82c07149100501c50707011240710b460003040c5180d0340e800107450000c411074a0055a5980d04600c24945080c01c3e1040040001d816043d04640c5048000380c0a03010003041d8001c9661600b030342d102042020342c0500098003005003985003d43c0d8103200b2640d40d42c28440458040c00240d5408003c45c541031803482c08030780d030040c01090060f0340c643c2110094200e402c00081c5454a079490f041240d01c1c8140088102d000107e80000e50f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 502093417 1250 502092167 502092203
    0x909030c0a110a05030c102a12020d050a0c02061c2301080705010509210708010204080106081603080a090f03080c0607030b060a0c0c09020307030213150507150e0a 72
    0x907111944070754170a178401e2a0020710364440011507081c034981e6081c07915401140c01105034070142c0b49038038441c0720a030b80e41220301001100701ca20b068a0f6081c1e401c5920703000441109803114424960240040356401450400518281d00240006269004011000304014124a00361154201030072442405190ba055542e0b400b010030070f00400d5804010044180b800d800a4880e11594800f580280155004100c0015800c8140c0c1c4000c03a282c012208519a1450258001d4000e4003440c441c0e5428840d00148069000601032510911480740c802214903541d02c04080b91701240c005418400c4100c070001d101051900280000d501840c0c0141d5101030200340c0d2030030000c0007002034040c58036040d4016400e444480c00e40f1080205230924444804031400e024140f95413a502504c03c0704c1c0000100100c0c02d074150050881081c116003c2c821542c2c851315840d1401d5040c0c11020000b400521400c00462081110f45000c04042c1c0300002c0c15901c1240c800b400c00001d0302d8240c034610750841e11a200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 502094667 1250 502093417 502093429
    0x7140609120306100302030c1308010f1a090a0e1e15010b1216110a0f06052203120605060c0106031b08030301170c060301031209060c110909030c0a11 66
    0x1003031150781070207145182010010b14103840b880d80d40c404066011000810103684801110054003407030000441d21075540d460f85010b001a040301103511410501e600801c0c086c110704160724034270010100340c031543d10340386000003d08140440340b2151040b032220340180030076424100303081000707a40a000020100c82e5941c51450040c0d2210580b903400700007600b101241d000c80c5a4000c0c160480907103110818550846a103003007407030f03000100d000e000c400008100c5910151200300707204a6051026a80750491000902e2500030414890000f181802000910440040074051212200014000d4855000c6010ba0b000f49420b1709450307640e00300505c180302443c000d01c0c800610034840803210798204580360340c4030300040c42005150b2070aa9805440a0010b0100b09100180a0403e90300d82d0381d40d04003d2080d000c204180303000f24080e8240443c040340700f0f10360a441c09070812485c503107407808402803281810b801000802d09010038800b0a4803000c0502244030498041c5021144480500d820491 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 502095917 1250 502094667 502094683
    0x5180f010f05010e010f050c01020d060509013303090c0611060109061805040204020d020c030406080705030c04061d040501090f0506040603020307150507050a0b2e05060d0207140609 80
    0x201c100961182000301e60307806030313001e07804280030728004106210b0041c00380c480e40600364862000d9400403642c400303c03e03520741c001012903004491810030303640d03680c9202050f044d0500301c850000300c4d44058030442c03800c802d400d46081a81071500243c0c0351465103d0030b070b5000d0503800c0322002a08030680050680340411205014000304101009094540701c00c9001080d0310402d02c65003581c581c00040e040d5a5143d0680706045890001555602c1682da6207544aa1060243c400401c0038070010450403840352040c0c034070031b00b41c035258245018201103054171950600903058090590310700300000140c80301e00549000702025440820701840707855030442a518002c042c0d601591510801300052380d800035020003124246031214042d5070310706004072f07081e10a410303010780341d80300c0c856490b02009900b0300c045203c2ca2031498564007004a81c22040c0c80c15241c03011002d101c2e81482000e1040b0318002000b0900d100c0e103480010f03d0425903a036001c0361901c01c809515869080903081283c1c4c2c406c10b0240700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 502097167 1250 502095917 502095929
    0x102010c1d0d05070b18010906030603170705010e0a06060603060806060a0b0f19050306011b0b0c0f1c06080c090c04060f0504091814010903020a060b060405180f01 72
    0x1a03200307240012401c940703001c0ca001840c802c00008440c403061040500072070b006072680501c0709643e0810400000f142440207080203002038403924000450502c07070f116a40550303038809502101700d08400180b80c0240c1020700103940f25580d4105c460781c0700108011801082c0c4c400c04000c6005807420f10b02070200c0743d0f0b680c40511150490810084950b480c00c61000a41c0c554449054644100c7c80742407080d4011007494074100200c107002020788075005400303148134001c2641c0f08114842081802d0864201d000f0b030007002041c0440116146890b01e0010b000b2210001a40c50300b000e00b140c440000016480d03008500c0a40d0f91203081c40040420300071342c001e55000784c0340d030705070340c241003100031654030035441960308200082032a075890a204070111801800d420a0038424140002050700b0442c00c00d09040b5211945e902052500030010f00604c4951600350b00600b800380140c1d1600b50141040042642c1c0c0090100804580e0765541c032215403815040d81d44015061820029100c10654103030080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 502098417 1250 502097167 502097177
    0x714060703060f0821070c0f0803030108070906060512062704021014040314100e0f1c0c02040b13110d0c020a0f0f0204060b0a020a060b18011e051008060102010c 71
    0x1aa14152001e8003940c0d45d0403103542d41c1d61081c5080241d0202c9145e00103000c55140554009401d100001c0070b5810b1b500284e082ea503515990f1880c200454206128160218605001040d130b503651600060350700c404090320149072203d48050003012801801d801c2d1603440300590900041d8240030544551a8440d4100f007210340c110081c09211600440c44010120b82070328a014a08100c2072090a00905000e101808078000041405d070700c0c0c0030880c0610107203104181c1000354510203103000c00d40800b1581c4a015680c038440d02400050401101c845400c04ae0042910240e00660f200303227132011101c96401c44e03c400034001500191503c10710100f0855004040000102d02568040d0101550105416442c0000e038030105024095944c05000303142808608484203540200b01c11001c00d01c515801c0020303041c40010000460130195800b6103101119005010900100140c0140d50307207898441e40141e5500d50020f0780c9903010480c4600000c2d284401d1241e196024000e405840441e410a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 502099667 1250 502098417 502098433
    0x30613140d080c0c031213030206090c06180102010603050d05030402010f0918020304060f0504050c1005070c1205030c062d1e100302121c08011202060714060703060f08 74
    0x40140519400fa103294445080001e8245002c40700f04203d9154080788034041000e4500b03d403114940640080042d405801000002180810b0104481c05c40040c020861414284203444854022004001c000d045d0741d83c5000201c04103d0811a02600561a03681c41d40c0e246014400140380107581c0710110207001d000a001c3c000c80351108490301140c51080001a200d076a5400c00e030002d032000e20811280646080b05120034807a010070a2907407540b00f0348080c41010710410302201d1134820198090800304400030240545060912030349803044c0940c0849003840100b1000c00c3c1810819604d11081e00b04c24201401c0c20503c000620700c00020f0341038907000d00e10340706003030a40c0100110510002d000b02980020460300504081c1405190040e02c0c0d40c1010b031a10744071b641d032080c916100e04c40388414842c5801d200e070300c5545001d05a8810071460082d01925909001035900080c40494602d04991413015650500b000800e11500c080da0307000c0313510307031078060745180c1101650441d8040e40c100b884 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 502100917 1250 502099667 502099693
    0x20d18080712091811040518090705060a021903020a02030d050406140702240d11120c0901090605073e241602151209060f0601031a03061314 62
    0x4c2c0c291003009100301040400700340c0c541d01114411500201d5200010300006e000328409a4400d5200f2205034003100c120507141c1013001143c2c01503d10a100580c0100d451002e50180c04151440c568401d0040301e401151603800039040c60040b06441c00003078400f003410001158403000174800c90f00d400c0c59062404100d50045291007004102c0e6949411190001c10044000d01007110440301c001101000203548490003920581e11100c2400340c010380840c041031140708464100e50b6080016140c80c0d03111441c01c0c0080d180343d007100ca4152010a441005d61110401d480d44c1340a80c3c0241884059206022010912010b008000c4560051100601d11000701c820b040100314060f00c1d920b0304946502000000f010392125880d00290003401c030410780c002c4204804043d0441803c0c01d40b600d04241e61700345a80d90b646004a42100780006130001054142d4042d0f0f0108201007034a40145441a4805010901d0030209480c50500003258900c0c0e001840300c4204c9050ba025200390283c01c112101c11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 502102167 1250 502100917 502100939
    0x40c060c0c0b1c0609020405180c190e090112021201090b15060708122a090d05010b030d0908100e030901030b13050c040905180d03020d1808071209 65
    0x8001d0310548900098044103c0b1031011030300d4601102c12109004090311403800402039009485000d010786846510109650f9038140b410313100e105450080ea06051005108800031b140c0248a003003170100c5128948095100c0104283c040c1800411615144e2010320600000c040350010905190345020340001c000380804546603008141c141d001c901c208800700009040e031007a140c00a02c01c49001a02104c0b074846064402c1c0300c0c19001540011425004455400c00c03030704418440b420f1441003084a6a078600490500d110074015000012400c40000200e442e2200d0100c0d40740100350001d07020440c00504000c0d042691004130018070071884d11815450340c9014908001e0b0605880c0d50a8200300d480d1043d054a000e1aa4801070180c0d0404141074841c50340710740a0504e140381407400107000d44402c5448125607000103002800750903140c01084000b500103a4080b106180c8542101c3c0c0c0600b030501e01114010302480203240d480c1068513080c0741d03260900c01c03414107010100b0340400c1950510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 502103417 1250 502102167 502102169
    0xb0a05190e07110105090106051507050334060603020f0102010209010804021036050108060303091311040806091006120b04080d0c050d06140f0d110402030c03040c060c0c 75
    0x10481071030303641e01c40401c25034040076400d10151080d0710304400c00640c41c4054015204941c01502c17542240040318611030858824000064000d9200300301000c5440310308180c885003002e030b1021810442403500c0300100306c0349000f407060b02c1c2207403075540600940c0f40c000c46504214400f40021450300e0080d40c0040e041e100004e20191203504250701080900703000308040c0f10200212006910b004000203190903035090454554210f40240c100085a00c3d40241c400e6801050020025070400001104100008a08920700c1c201a07488202d0943c082d18810301a01c05008554084c04052521030300301468121a00f0a05a0b168240801002114800100145425003080038036503256a03030305200041c5c0c801d040c4402891490b00383d41491f216030250203004d600015070030030302203281d0320a422081032400004080d402100300722084120700d0055904403c8a01c10008041821041c00014003282c008407200103d03094000708001c100000d811041c40985140d05040e0318a0850362525804500d01e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 502104667 1250 502103417 502103429
    0x4060509190e010906020a1e0206012d0b041413020a0e010507030e0918010515061c0f0501120c080f0a020105090d2a090209150a05070c03060b0a0519 66
    0x1a80c0210031250100790406214150885c82c103640c0c407034406000030403103d1035105c400a48101030034580320039880418441c5c125020050314a21561950030506058421002c00544200c1800b5000403042c0d41440644000c1482450404a0081d5030b001d01045010b910440498103204200c004045500030408569880c02842c00a07201c00c01443e055504a40340705989601c40c03015400c000c14403041300a95800245a100240040e480b14256140000c5807603280d039510403400d002012941c1c501070400ca460450072013000c2480441d2150b003d04a90080c1c0120701413031280322125052000c070f42c150703400070311745400100b590040c0a482c040d02d80b1f02c0c4070f0000381000f000180e4403116a55605031907402d6900212008140402882003080b495480843c1411080340e0000000d40c4842034400d8130034102014205071a2140c20340030f807648591111000340309000051060201007140e411440d0b000d1403240c0000280d0414800402500708400c2c0d01c4140715600c24880c01121180d41e4845030b00b101d507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 502105917 1250 502104667 502104671
    0x9050f0d030e0d180e0906070f050a1d01031508011515080a154a0402120708030d0c120501060e1201020d020c070f050a0815100306020a08060406050919 67
    0x160b10713019054401229403120741540d101e2402e1020300500800d20900811890b260000d0480002d0400d031082c1c020746800d80041580c1e071070200c030049080282c42c000000140f400241590584a1150b0750b856185c2010368540e40d144200304005082e4610b2101a000e04910b2b03010007880c8200040c454100144490203094403501c0d00e580700c3c0c199404c440003900b004507a403241500e0250300d4480109095400b01c24120780b554442c3c1c0c0c040d80240180d900c5961011403200e1607501c60b000d000d0000e0b40400052060711400400241000d07043c000b50080c040020004100c50003220401004034540d0b03560a6906841c0c2401006100e400c0140340400190983d148886080b5940c042c40c020b00500011700d6a090002170f0700c07801c0c9500403414005940402e50b0fa08116500c0c0d206201803500340340102d0905a004d00001c640d54990700711003640c4040400c0c03045190303d031a45c0d50344040c0c0c0c0058100c6400300e0000c809000542c5000c1c008e90340a0841541d4001892a08130980c001047c150840074860310307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 502107167 1250 502105917 502105937
    0x9100c0c0e190f090206040312181805091c02070611011406040906060b0d060e0c07082508160302060601020d1b0303090b040506060907030c08151309050f0d030e0d 72
    0x1c00f56400039030310150028015511581d603820600b00201c11701c2001c0000594a0700b150030798011181c0c1c0355054491450303080110707044c128803400003400084d00b292024440c0c00c1540404160283c00001002860350141000c680f0741400a04080104255410503034142f14150748103400216040c1d81c0401c00b140c01080303c10300340c108480140220380002c3c180c010001401200c101d03054000004689111a40e4084c560b51408006803070301031f0701002080307030030100529407c01c0380c503450b03101c00c1401c88111603070000503a5a851480d40d000b5500d43d256440b50b4010441031580501c0b005912043c280040c10700700d039403101c0041c58a003c1d00c41c480c1300e8401004050007410b210b0b07807200d0125507208440c045241402d062055596008583c258810440c374400514254420f0040f1904548035850b2142941ca46a1150b010206030640c0e054005410310003443d034104481c029851954015806000d00c0141d011040341007811240001060504004200300800701c0090f0f0040c4030180c92424034400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 502108417 1250 502107167 502107191
    0x10219020d17092403040f020a080307110901091e153f0305030406020714060a0f0c05130e090723010305071b03080a0209100c0c0e19 59
    0x6829000281001d07204004112103211568024402d18404403000380703120215132040e200000c918811040d10642c24000310b00050502c0385113480303a82c40101020306064a6140181c0b441d0040d190035203984030034a0800c8000e00b0648401400b50070441c03824805150040030480346440c003111041d4085940d265400d1081612000102c040d26030704004100f041d4240d40c481c0c90055602061502c5158181c90442c5241141c2101c0c3c09407940c1034881a0030340c2c0e07551320340c0c1c8001c0d08032040965850740503020071004803d003400664407030745c0c0c4210005100042c0850700412a4010701d1140c040c05020401d211500302c00060090455480200540c003503560004005e0801c0c06680c40724140041000c041401d40032081c2071954068020390b4200100d6981c244200c3d0303180402001101e888650040b0240403d1052040c039038840c1c50344034003528208400003c03c1030040185203080005d040d500398003081101000740c2038024000c6840350b2125060643d840d010589020180c0c011541d40c0300074100c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 502109667 1250 502108417 502108429
    0x30c010c110a03080318031608090109030c06110706080c070204020d061505030a1107121101090c1403060c210405190602030f060315010b0a05040305071d070306030201021902 77
    0x20001c0040c00a003202503980c83d04c48190b8000f50b403c0b0b4003c241d210600011718000100b9070700c2403411000000f034290150744446801d40d02c591f0406042004020022010444003100440107000395078407003445003484641c060808030180c011008000c0000240300114a1540544107150713011a070040e41c9581d0b041c0e50303400802c601d6002085d9006280313001918150808c024500c9005020b40602440b02c03003042c090305903c156640180b010a12982036603103540f080c10540414200a4000100c0c03d29584880004e10070329071102c180045503503820822401c09029086d00940c681d44a103080c1480c0080c901c2e003110006681c010040724100004d024000e0810002c202100842c0b07140c80740100c40c0c1458030195004a5a40070000031801c0480e906090005410040c40c0012000914507400c1002c2e090301c5500480e550010045c080c800800494018094071004154020b500d140c8a24070323564101c0b01903030081221007031500d041410405130740c01103090031810000b01502041c003d034034400659 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 502110917 1250 502109667 502109693
    0x2d0e01180b030709140a050610030c02012406020c09012105032205040c110607140f1c1d370c0311030111040513060e040f020405060609030c010c 64
    0xc0d041c07107554000120100240d102c1d14405c1c8200c031400151741c3d02c40043c0b005848041d00d0b1140c005c030003108011819032096002004100e80c0c2c0c03001081050641500300c910141b40c1c6445004115099410022550104044405414265440c003c1589440c1c0310080f4030184140c805000900c1161481c2044402d1040703920b41c500c0d640b078032034604025a8a0012880d02802842d000302d2524900119860003016210391125403100280803540d00d00100712107a101610580e805036000b03104494690101e03070050132070b00001c3c0c40f06114441c5000241c00075030f03403102803a13048410300500c40100e041e800701c2e8051040280580d080b441203041c69002c20001c001c401080d9010003c0c02c059000c1040c4451840c003200e0099080c901d0b0810480c08241c221041c108034900c95120401081200b42007010b00848440003c4030001003445d502c231103881030401c5c1110202d43e1328540c04000c50440c941485a42e8000301c0989102c0e04181e07078079003c07a42d200854408241031085c009051020840540e507882c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 502112167 1250 502110917 502110919
    0xc0c0106180f0c1b020f120d0302030f0f19230405010b10020c101b0b160807031a0d2d02150703020d0503040c0b03012d0e01180b 57
    0x9250001c000c00c40c900180b080300d0074121030b076082200d03040041e84250b0015002e050707074004e0400448038990030050030303042003009950015000104010059010301216000410580300580e617441d200c2803140c106030005014003030000301c00382400610552500b0315181401d2040300080d85041e00c18246c090161040c44d02882c2980c4241003104001042d0040c0c101024191214122078000210581e1110451140341382c00c68100c0e00300b007071441d00c280303290140f03035605000c0e00075100d855844480e4001d001302d900129401c541c1000000040d0b00006280d806102da03d400c2002c0d2640c880c52a98101600190038818501180148184054440d0074408603800130700d1400c45100300d01400000e48403080c41640725480a409400300c0c00240421914141c1e410b43c06410380c55481481a1740580000c0c0065070310038442400840d41500030402140a015000c80b640c0c80c2114a00c20043c5014200010b401e400855200401200d484200700c07030f054a010011032034504074421325000c020700d075806081e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 502113417 1250 502112167 502112189
    0x121009060b030120091003091208010e100503070b030a0e011409070b0309030906071b0906140103090302060c0a020f0601031a1003030206040308070c060510090f11030c0c0106 77
    0x544100200c0da4058581010250000e1100c51801100300100d601c3c140240704901000300179203009032070a182511301c4641282000208185580c45402242d0f0380b42c441c90000c524a040113006407592115085e9226103007882d01e0041c5070905c0e000c01c2e01c07255940706543c600c0070040045040c024083c0c01100d440190b0300005c00460f401c965444014178010703152015203014070310700400c210180204913031203600894021450700d5058401e010055100c0c60303040d038202c460b00c0c0101c00d40b1100b0091b4a401451811004544075042102c01000c035804000128145807825402c400020f1700820015844507165008a450b20003e4405030b050140320b0849900d180900e40010007001800403412000f0003d10f003a8010700e55402165072005200b80c08080c026a012100203000244140807503988100103140c601c1c7e0b03122060303843c0340a80d07405540c402500030b00c0000601c05e00c0c0180c4140c030308a05c650b0078203215020040c20007064520001d00740c6d15401000148400700003409410600c0146203060034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 502114667 1250 502113417 502113431
    0x6040311041a06070614060a080a1e080412020f0d11010804030e0607030207090b010203070b041b030b1e0703061202121e06090d03060f090e010f0c050a020609070303020a021210 78
    0x100e00010041c11518161b50b603201404a400703401d015001d4019240a0001401c19480035181c241c0303404100d2080c0d10000c418541c03540001486603001c0c000074142180d00c414548071a104110361800c41c250620300600f01d911610f404103008548060208000f800d2400700e43d22070b4217044807994030400d44550850b40000c2c00c00100765000400c202200c400b407030100150001203004903200d2203800da01070220000f1102150100d1000c052510921306210080411a41d503503640d03500003034044840e002204000e0300c00c0400400620a0690f10841500d0700300410750030121402a1048401402b0303002d80c0d1080d0030314569030820050110340c1001002c4520700300d40100c41c4155114000c40e1400c0e468042e80000d807000e18080e0181d041500c440ca0084007071386062000d04d030b00418001007512615900c840c1c0ca141d0402140c400c80c1010301c260380d20f0903952495504003034640100501034480b2580403040820100c0e03804540c1c148030700d034119551031545185100b001d07c0c004a070314054170345510300780c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 502115917 1250 502114667 502114673
    0x6040608011104030c0b03070c121206170606041407030b21010c0207121a040303200414090f0103081b071e0b0c06060f03030f0409020d060506040311041a0607 70
    0x809441100d115002003860243c40f06c02512040c0015500c0002040791030078000001802000703602ca441d00344e80b174681029070324902c80001b503031400e03030001e00c4414200300a240a0f04c42800519030064040c5e4003071180f811444c00a130500322006041d20109555403011040c01e5a40d0001045900ea102c0302c2d51301800c0360405c0080c02480b01d0741291b0b003d40703d244000540c010703c100c9107080340780d0004c920540d4035490340702503035885000400840815988031720070a070f01c0340140240342c1c1c07c41801c50903540316810400010405513440e00e1a602c2229810100512050103510722415242c2c094045500c0311102d1088440a00141d081c42030701d401000c0e804034082c00ca900302c1402000c0c503c400066516690b81202209104180f071032126500602c00048180c144902010103101002e0300b246d180c41c0c00c05018045c0c941080e04800f01581c0c0001c1c080c032009010380922070103044111a250701e001c0c44c0d1b60750081c50101034280207000390f8031480c0e51410711140c85003d802400010f4a4036a031980700b46 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 502117167 1250 502115917 502115951
    0x60901120f0e0717032b090c09051b0d020d06050a06170c090306060d021219060b01020304060c0f0807020a08010903030f0c02030d0f0b12100b03120f030604060801 72
    0x10b0058091841141c10000303010f101080c5844800c1610381c061494400c1e01200020300c0c2034201c240b142d0300b106550003003075002101d1082070701403409080c440c000982008200c0003660005000f24200f14000b058102c1c072140007000711501000944401640c1c0c00040b0f0200c1e004c0d1500d81c2c41254001900c0c0030009649800c910904c21008500702d1359400c80da9410000c0805001e02c10394039400d40c1c01800040e12504144182a06050008007a44980c1c0c0c2404040f80c5000f0030032918200c481c1840c1c0b1100d003001314500950002c82e03400d0000d18105030400038000c00440019101030202c6a60015903400c1c84006800c8508480c1c010f03140c100a5915140c140c1d010700490b203c202c00107840c0011b0503091100f5442040c181c0700c0c66901552400d160b24801030301400624440c070aa155031001c514034580c0d52502c4d60403c2d081e00001801c400e4a14105560031a221214842e000c0c2d08078445541c0c0c806540c4049903208850f10400c5034a0761190400300d00180f5151300b01da101e40d8a0103540d00011401c036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 502118417 1250 502117167 502117181
    0x1c180302041518090809010305040525030c0e011505030a0b0405070804020f0301050c19050c07032a0f030f0f0b0403110c031203060d02190906090c0518060901120f 72
    0x111a0310743ea00c0302c28402200c112016404007400010040c00020629031280d000560824051011a400031030030702044042110f801c0700144c4c84004510041040110100100000707115094038440d0072f61406203680580400d458002c820442c0000010755104481d5101000d0400e01500030002031410002c05440d104041d0b030160720030900e880040d00c41d0315050003460303c600b10041c11241004040b220605007111150100014801c3c1417040c080528000c003e1f910085019120400e6009000660071030200f00c2c468140c0000402c48800348058101800100300301e0743d00291700e101a07420781c00c140b0360030007140c400109158081c506000c24903601c9908540180020000d1340c01c4140710b10101555440d00c1c05900c140703214240006580c0d841d00c111184512400034003048210486825204c81c42100e40e0080c0303d0789659072009114141d454498030441c2c13405030074040d140034412150201ca41c40b00440d400e11848000641009992107800c0301f40d03509041030000d0008540c0c81516001070621 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 502119667 1250 502118417 502118429
    0x907110a0803240f130b0d12030b01090303090b071a0a061a0405130506040908071208060d0503090409080d0f09060b04050f0414010b0d05060601030606021c1803020415 74
    0x1c241c6a9420454002078100c0c61200810b00854034229005104002c9460130f42c1111701c84d511000c402264440b95810000184201140441c03507010a10250498900b16100341c100000104e0502c0040d402c01440c0c415120180740385502c907421803a1645c01743c00c0c0e1800440442d03004005101141613940c0149060741c0b0804c0584001103800d114007030260296100d0300d584008060308140815116034091034020304094004114400d01e0349444450307510000080398222030710060100303a10b138484011030300841c003120744001d07845040e00c9450380da00a0300141b521030341e65a501c070020044501c1c2102ca042190035024083d06100c2031070000106440701c0c065a03014104001c820b10382c9803521800b03100700001d80420b40c80d91a01e403103105500d20810b1004e07101750350b103008482090703a8291604079142e20810080c0301502d0000001015186c0c140d01400555100051108040c250040300008034181440c025800c460b40e03100344402400180d00c042d40042c500724400c003034100d400704d80e0015900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 502120917 1250 502119667 502119691
    0x3051e0c0c10050c12030c0408070320040605010801030201030221150312040b0304120c0b0c030a0e0f191b0605070c1e03020607021816120506030601050907110a0803 73
    0xc2c21074003a1035501c540d60b0100201d03085400116801c400e0640555040b4004441c900d0a01e52226010780c44e120180c0c00c140e440300364228000700d24401141c0d5044d17400805031001d20080c1e107080e002a14801040c00000e0500d81c0114115181c00c42648444400c550301e40c620086030704184a00442c2285400c890b60b0180c015001340b070b080030b16143d00710b074203e801e1038280381e2540d0b40ea6220701c10701601c4510203c0411044204e240e000c1241e552817280652000d80c0120350381d040c2100c0130f4045412841c8506050341208011001420004c6a10216604180001204005a8a000c1441800d02c810340000b403c25101c1c04120580d02c003000c0d0042e02e200701100f504080d182d8002103411030110310100f00e5200300324811f00041c204072000d4075405101414440103a080841841420305040310451660420456410b40142e03010b40810481000820300b0407650400202103a110781050040c2401012018040b41403240300300714400303100e00f1000070380340700e040c40386009002c030350098404540041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 502122167 1250 502120917 502120939
    0x40b030105130201080711010c0513090b03070501051b01021803010b030a0c15050f0703111902060304020603131505061009080a03032711031002031303051e0c0c 71
    0x1050501c10140101030030391054800d801a9801196590001030907201004091103038071400c04024084c41d003224030340d0740303030652a4091042c1140b0804000e50003841c80e01c3c101038200140e03417408500d40c8286e500a00e0030b40e945921418881185410a8580503100c1d07100064070384070303008a10400300c1061070480c001d1014556076010181e885411000140070701b00040c1c0d0030009822480d20358140c609042c201242005c00505840c0301a400803442174003c0760307182c1502800310f130040c4003440000c0b038900904201c0c100e45801042d400d01008100030f01410001002c200300b5207000b10089201070f0720076400c82d69402580041809860306440340b070701800c3c42d0740b8011441c0b4020501350058600e144010032a40b80305840442c06002c45a640301c143c888400c030580001a40006808030b2140560841d15643c042d21081c540342009429000c1c1c03000d8818010700c0404001d440c1a00161501450119215990f41c810601a221402c10340d03c03200100140d100b03031040b07000c120340b050340c1c604903aa0b541070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 502123417 1250 502122167 502122169
    0xe13150b0703050d0e0c04090318091116020303040816140406030b04110114030c071103030c030403030c030e091e0714041511010203090f071d04110103180c05040b 72
    0x1030044140080c042081132003944001d0400d98400d4078a42e02c000100c41240c0c0103c0049411101d18540c00e8000a02606000d103611480d0400b4100070b1444240402031421807944a80d043d00501c04103100300e15151509070150342d010401e440190100c042030f10f1074244400102d601040407403242c044041c260910311801441c0c5807164030304403500035648100954956031112610428030303c0d4207042c41403201030640350740304000182d80314111503151030781c0d1114903007082014000c4900d00c1d107100342d004003c922030190010013076400303ca03490f040c42d01424410349015201504000d4140350090005c03c00c00405c03000079403111080f005120803540171a15403840480d5458000e402104420b00c003000100103190203810700121010b614940420340c1241c0c085e85d5400c0ea4410f84d402051680440220203107030005208190040c2070f08100c0041c0c4100784014052000b40091001d440380580001c1d02c0c1103030b406074100381303089021210700749140089490b103d0001d035818081d4034015840c0c55101105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 502124667 1250 502123417 502123439
    0x1a0610051c0222181a0315190203090106060e0306040c03172a0c010c1502090f041b0306170703020f040b120109030e01030212160e1315 60
    0xc41104a155511414002554020303601000900d24484910040d50034110083c820742d43c0030305081010001003c600c0003552094600394055007201d03007000004200540c1c1d00240c00da00d076801c0c2c00503c09403036586040b28189034210100c079880040c00003041194040040d41f211041d00d000b5110401604410030038181d40e1801210010640c1c0c070708403001d01c0451803040036074991169010724a4640742c00381d050301080703105070802011801420307041c3e41d43d854400d100c0d40d078a80710b003843d01d07260440c001c0e1200c03046211a41c0080c0802907000841070882d0b00d640c000c10344685005881803001c0003182100401680da032124010000e49003a20220340e0300100c0c070380307030046003011002424458215002c022103214040e903d242c0c0300382c4d240007a094685400407101880d20020307000280307501c00340c10003400c00b101480485040501c10030050006500003070000f42c100c3d900300f5102002903064001624004101409280d001170074900a15000c00b9035046030240e03403034800e050f0300c0c02903a445c00307088 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 502125917 1250 502124667 502124677
    0x100f060f05180a15032a0507080705150f04050705030601080d030e011409160b0909151809030408010605100e090408190504062c1c1a061005 62
    0x55800c0101d10407602d05180040650700c8014800980c0c90368503000d001691400048400100340c0714450303013003003c01885045201c00600c0d510720664100d0360200425070310880e400141503030008100081030110802c11921010030170108900b060504c17041c400300c881000c642c1101d0364480d02c400842e25040c041800c41c122110503008240a1002c0d00c425006011b4000e07503080f1941d40c4400c2c508071218404111400781c21104054100640140c4c84c00703240c2c58144c1c10940d560002001400a40e8030b52480059000000059004120050000144002071224254400903810344144200f51070702100070802c45100030001c00003541c1d581c05014502c0143d02800000c00e500030840c0525040450000d0350161103804880d01e0140f1400d404511018080460000100c0118060048030f4000002500d80d003101100c00d115095140002151110780d200300e140921440032011162554289400710b10582c400395511003000305012002c42600700f2180688030740f0301c2844140d9a03d001d501125 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 502127167 1250 502125917 502125947
    0x60a0b0405150906030411030d0914040c0225150903020d141204030b040b0601050c0706050904020702040e0d02060115050d0c0e060d060e0105060f03041217100f06 72
    0x80d04007460142005102c1c8180030302d0b00c030b0340c020810400855581307403802540b180d481200c1560241c01b10000317140c5066400007048080c006102c10910103901042034029030707044125008103400210200c00c03803c0c25002d0b40c0e02507111200790703084440d4a01e42034120080c0c84a009c1c181c440080810f008548148191202940001c00035021074040b605440380f1042c842c40d00b00481d401051002141800d982c0580c1c02611019020824442000010b040c40398208109203420781c10400004d02e11900c51102e4402c90b81071000006d16001143c449030191110140c00400400605a28045050302c1701c040840c100010f0007000004140301240d840418405036580c0e840c3ca003400c8007a20b1920081c0811560300052100341d00700c0002d01c5d6102c02c01050000ea0381750340411400e20b01500c51f2a04501a04070300e214400500c000840540360030162030307100e6000340d1301c03000c0c0500480e03090312080b08000040c0c00510220301041090f50800d106541160807080407004200d40d0b800d01207629506003090300c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 502128417 1250 502127167 502127189
    0x90105101a0a0219060e1005070e01120b040e03120c0c0312071202030a020a1d03030d0f02040b13150c0c050904030908010c030b0112050606072003060f0f060a 70
    0x24190341c00c508080c01c0d6030345050040f100c1c04501e6042c11010b403110321904950a42d03c6050350b03203e0107414440030a18010200d0305200303d0034281030107080b01080c501103a0400907003a0381d455000c000e9400040c0c0e80711001d4000c02c030301d51030b4495168495100d928901036801091021800d02d04210003110b1160051102440c184400c550101c0042080030b440030040040044046008503500c1c4025401001da500005036642c131030807406000049502c0c240280311200098200f081d46002c02100c12400c00d100c00060031302c816186039402400342e42c2010764240b0010412100220080c1001400e40305000d03017000d00d10100c00001c441c880780070359001700f10f10007803c001c01c0310341007807451290020f102c2c4c10070360074058072144060b08480e0040c10990000340c0f01c1640e003500796000168503a0391500c2c0d01c0140820701c1e060001c034142c0c0c0b1400c0320040c40f40761030340c10303d490b1b03400c0e608160036905030000d007036994904041c044800321200944d620b0031005040008140c15150810029084825030002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 502129667 1250 502128417 502128449
    0x2030c091e09101d06180d4e050c0d02030a1e0b0117090c06071509080403020405160206010506162916081b04081509010510 55
    0x404115240034088202d94450098041c0761079032140100b0b01d8001d41440c43c481800c00c0684031500d8000c010308816098000c031541c2c0b60070380b00c011580060039626070804411200300308a240300060740361100300b480e2000d039111142100000d01401d0032401e95443c41c00708415000c0030b010048540541d18a40109170030404c0140041c1c49402071580100c001100281022403010100804100300040c64005561390041c0309441da044046103140d0b01034461000720300c2c9030442d4829a00c034036102d0b80503c1036001003500c80401c070814107501c1d103044001c2c07014050310300030b450b0202907a00b0601040b80310300d080000041c01500707041000020f0204035801040c041c2d10701070620020f9072014a110b80b0003500c0c44030314000700b5200114820020f071480b40b0203900500c000940b120410000e4000007031103481c11001181c240e0b01c4200207401c650104c510b00340005614094020610031507004180d01c0c040c0041c2070908114a0786040d00c1402c0c004000e01096640c00b00d280780701354590055103426000380d41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 502130917 1250 502129667 502129711
    0x4060e2803121806150b070f0b0411060c030913090b1303030b0303040b0316020d021c030f0e01020703030e011b11010f020f03150409030909051b0a02010902030c09 72
    0x40c41c05402e01400384000b40403038000c00c003600c80c48820141a10b4080c0c903080f40c001042d014425440c010114040d52901b404190345d03c0d0194131a0100c40606803281000100d01400420402a03120b801c004282550b11041c41201588a411900289105030240b02d4540720104040c0650502954040304d00300081d95102c82e840c00c100700c0385500b50300701569070880580c16101003004101620407a8a8580c4074586110528032030008a03000b41c0031900095801e12000c1d40008100c4a42c6001805c40709030b50443c1c51045000307118940a212030070341400c600001d00b540c10360041145500990b41442070f040030380354560031b036504159468030300001e800c10070403c54419088070f00030315080700c00403c0410071101114266004585481100c070310000500100b050b00595086a11206a5061180d0032450318041c0000c0747e14820b1a240a440300f0000324658a1800c0b60b140011042410540355490100001d0007011000c004030f02038850120302c00c00900d41341c0e000d00d1091010780007094003011030030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 502132167 1250 502130917 502130927
    0x7050f0118142122060512011d0705070318090504050d110709020c0102040b0c16082a120f06071d09180316030302071e0506060405060d0b04060e2803 66
    0x44502100040c003034221302c01000044c1400c4002d09059444030b03202d096114a01c20804410380c041d031401d0f48a00039030a07030404028000c5a01400c0303810b04d03035101d2016042c20f03111910308001003004a240c80c00c01084c43e890303503448607000e10700402c00c035100b500b6203440c01d0321420061081c035200c40c0c1c08102d00700b01405c00343d00203140c5240c5040016040540d80e810002840d0024250108103170080c600007604e40780c03100180d6009120420090581c02d038445003207280c104000e60343c01240c0104100154068445498905400003a4001c80f107940c1d070020300031501c54500b45c0e4064002030014040c244045c0040c10005541c250040640d10b00352504400e8010404803c84c03450070f18041031080780591920120000d280c00c0c02a100980d440f00d01e40790082c0007036940e00c001482910300c0c80061011031000038101e503008209940004407030301c4413800501201e0980c54001e007103840e0441044200443ca400c188681303a00d080445600b80c64008c02d40e4004404039003004501040c420150020900c54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 502133417 1250 502132167 502132177
    0x906030a02040c02121201090e03040e070513181a3007080717010b04020a1b081303080c0105070903050a030525031d06090d0807050f01181421 63
    0xf50040700c10303044400c1c0c141c00ca01d400c0360380e030042001c0f42807004101c440d88600400c6012182d45001c0d51602c1d04024090b450410080d1101c410004e0100300c81c5202c0b4041e010780c0000c0c0c99850410000c88810700349000241c0b4001403c6410b02d82c4c8101c00030302c0c40c00e00011124042c0f002e480740311880d0740b407805280b080119004140c14a446003c00000c1c4540080c081207020740720707e0709540e0912380500c0e1440e094481c10444035005a00c10000c004625134058008400d4070064555070189440c14140088913004000036860b0810011710004100500100200310f08018440207102c0360352180d80659400d911844050100d4002d084a880040e04c40e0b4000c0040c421345281100b58040d0224003210442d060403412004502c0000e54043c5842d000024200c170180d0450b00c2904e80603000c008101000070b40e280043c030003140411580c04004c03080c0070015010590b40300810160860103030810038803c0a06040c0c4010880010180c164000032402e405605060146414030740c010007040b07001a849 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 502134667 1250 502133417 502133441
    0x90213021c020c01090b0f0702060c070804120303270c0f0b070813030f030905120d02071e0b0f03010302090a020301080d0e040e33100303030c120509010207110906030a0204 76
    0x3c2d8150003400074880c2c1ca01d05000307d01143e25031a061030300060291030a03c0142015000d03100074042344000488400449080c2e41310041038003006101ca01d41980034000c0304c0e0602091089401402005103502c4400328031040c02280000076003a900c2060070509500c0b0b0207001905402040010003240e5940c006048460082a0010b489075803603c80d500d040c01080710480005000410402080c504616980c0300641c0c107a02030070688804480281d82d94015200351403100011030314903800c0c42c120000510040403040c440941e41e11403050305407915070090200720700c101c03405008152607000e070384207490684410700000c06821030002000d0310000201e400560348a41c444405010a070810b200030300b440d2001c00340d160704005105240700c80352071060200e644100a61b504019054407070021140c1101d800d428002149019150111a00c00d07a14180030242400d050074410304001c150300a000c6c0a01413410105009440c6080022564040c0c407001c1e41035106000e92030151070150b10041d03038018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 502135917 1250 502134667 502134671
    0x9031518060403050a080f060d1b03170a0908070305070e0402060c011a0907020a0c0e1510020304030c0603180212070929030c0a03060b0303070c0306090213021c020c01 74
    0x103024014030300e01902254220000341010415610481c1c221034160f400c800000400620f070720340b050100303c000b41d0243c2d001e4075442c503001c01501c4038038002840d0030140da001500c407001c403134080c0040340740350b070010f07601c000040d01d1090000745005020841c4000c1d00e0348031019100e25460482c0d50000110041c000340d0348004100012004c1d90824891414003002e45c006c1d030b400d03902c000320802ca1070a01c003c01c4c20080d5041619240006091000713920241c454956943c84136032184080c820201e03460000250700800300248851240b50000094800c80c1d115030038015601c0d0715100114145c4224030b9100f110011092420302c0107240a2072843d01c000c0004044031607950b0f48203d014181d86c0c500c00300c200fa0314000e0802d10140e14070703540da0300e04a950607802000e03984001e002142d8408150f11000c0d1845130741e506010001d980a10032501000d0b0888594800c3d41d40303d0410000600b0402d10480c81822800c0c85802c210394907000ba201c4422079000308111030032020900c10041c1d070101d1135903840c41d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 502137167 1250 502135917 502135951
    0x5071104020d050f06060a121e050f04060e1504020409060902061b1506100507141507020c040504030f030b0f060706050f0f0610210f050a11090315 65
    0x5100c0d40302070029020042c2d008169420040800005220302070040c2c0d000d840e0401941c20140c0d0440414900500b8400c0c00141803000c5102108180c41034103400c00c6024102424861200318814101e4011360256004120109100d803120342e0700e0b02c10400d90304201821030000703405458140d002c266100c0c0a1400402d100507240c1c0056880c1c0c1c17203140d407071400f0b02040b80300314021441040f81070f609a00355a1402100d00345000011980000050144108a0005040c4040148100a2901401d03d000456241c02860248420f500c20202c1d800d10040c46038626482c000d00d040c1c02850b002e0360309034a800101e801c2412040f8017420207400c100d50015054101121292070b000020054140904000034403800c10160211112502800c10416480001d0a0154070341da901c9a03400f4420950034019006031b050302e40151400e40c0c540d2240f440c145403020301403034443e030307500407504c5000f100340304000114041344180d15a0040a1150790181d011144190190701c00810310b64010080b81c115030088 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 502138417 1250 502137167 502137169
    0x80606121011030910061d04020a03140d030e0d1707020f0f1b030a030504051908011b0e1002060a180804030c030605060105120604200d0b120f060106050711 69
    0x150740388000070b01050340e0000800085040500078603418104212092002c5850f1050030345446003200408000e14142002050441d80c40d41c0580e4021680441c5010741d0240c88070701d45440d0b003103d500150101f4145082c6611040c07003c0b45446250780c05480b030618581c03212041008000005002d0801c0d0700c80c506020303001e00000c00080134003c4a40b0300400340106080001d0b03d079840c0103607042d40681d02c03083e44000041c0e0090251020b840085c1c66141e41d01c2405681d12605242591001480d07510341101241403043d15081100103025640710f01e8500001d40c018421803003102400c10005030095000709a621070f694010348101090404c9904403210340761142d015a50150707104545a592090f0200100905805401e910500c2402c0480c101846c3c0390b030240a00f1310040905104980c0c40d642c0360b100700c0c0024960305420140b0b402054450412b030030300800816010329081d02c542d2507264602c6050000161031800810300501518035a4070701003054400d90807482c4203c8544200c20808051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 502139667 1250 502138417 502138421
    0x18060f0e04240302030d2d050d0c170f06011b020409020a080706140301031e05160909030806060708070f0807060f0209040b03070303020d0f05120406020304020112060806061210 78
    0x282c4039004500c00403082c9140304061800c00000c10000038000c40f1240100365106071764404c1081032078070952400d001c042e682c0886481c85000000c0065a15118610400990280711001809841030050a940c0c036844401801c0b84011560140044e501c400100156000c0904241c0280d101420224003225103500181e1141002d8110100c69170110400304061030744041803c0e43c0c4c2e004c5117403040c6194150b07110178072807500e100110640b910724a008202041710400120540951015407060300f00d48841200c4003604206805800003411400450940c0c81c140d82141ca0096200d2006894203003a503451119059034018241c40a2105101000114202d809195119848220010394403420981000308550501d25420302991118006000080d00041d05c1d580c14001c6003800c01c0c0c030040600003100d551042041030454070641c5c405100c100001034024502883c401d072140c0404040442c43c02088a6080c403503501c1e40e03481003003c50800d042808030b81940d001074405075080c005085c0c0b20001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 502140917 1250 502139667 502139711
    0x190c050c0f0324060901060c050a20030f07060905031615120906020904050c0715021803011b08010b0316050a030e160e060d0c090f1b050a18060f0e04 66
    0x3143c0584208219807441c02c0c40d9200d014140600b041c4a0084098407100d644541146004040700001c1001c481c9040d03103c5403140c9840c00080071160007040b0300350710070703184c103e40d02c104000b02e140145d005c2294500464020761502940c1141e008a901d031110304100d260701320f0383c40010721192000d40802c0340b006008180405018640160713030340c030000040c40125075009140c40d200030014801d0100013000c00c50515148405641c2c0542c4a0600e800758502614420400c00d0345986003400390000c00400351243e1075036076031a80721400c1607079a40c0401e1025204c11a4203400c0720906e04580001c050280d40507020f082654540003074180310407440640703005101c4041c006e0105100c8010002c42990594990384640140c0c0d0304038911900d5aa203200000b00740c06000f00883e240d040c0c0142c65030599003e04040b5840b540d503c2c41040c8008000b608640c00601c1e054005904000c600788400c20864403e4111a02942c40002680011008441109144984c5680207845421001042404502c0b0503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 502142167 1250 502140917 502140973
    0xc0c11061207050c1509061503010e0321010501050f1e0403060e06060301050c0f07240603080a02070f0f032010050a020f0f120309150705190c050c0f03 67
    0x59031140c1e00b4110529001610340d001a8111701d41c000c0058003000880c4a5421401020303071211001a10070019000d0460454000803520021860b00520240003000c210001d81042401c1c8e0241d8a8800459292007031041d4085d5007407040111856400f880321040501404018206050a4881d5501400c0e58680341003400c950b030010080c4100740c5020300ca060380200380540824500341c040700c046511401100c0b000341001403041c0c43c0083d4480074a484401c48560b00500b081000c0e200d241408490300a100144018405c1610110b082c500c50403120080c0c0f0040050b0350162842e5a46400041c034841d41024a103d1100e0796580160300c0c1d16001e0740030401c080e00c0e050380f10b44903154003d01c0d101943c0d00755103082e4170948214175441070104001414200181940d5034986d140c0503110f00c6c0c4080300c01c3e05240e0070b1440f000c210050303920030090503241202c1e04034134903262040700084510f09140c2d200501a90000045201d2910344181842c110142c0071301625941d03400181d91001d01c400c041174035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 502143417 1250 502142167 502142177
    0x309091005090a0c1205060a05130b0d0303050117030a140d0b0a030c1806030c03061d03071b06181509080604080301170a0c0501050306040b190501020609010c0c11061207 75
    0x2074001d40d40c000313841607145c41c21032100700510301d400000203440c8007040c46541d000d403c890103111050304442c4c02450012802808042d4840014600107004081c240f150746213911090500220001010040b01c144080c1640c69090114040e60308400e5948401c40c0425484e0b5980c4004119131126400c02008502880c0f03c0c3c00c0c0c4919045056507840300384544449014900f02080c00060b100381d4106003642c6d0007120000f4240a500d504105410300c0e00f401c415503200c0412038904000d04807a103c0504d142c1d0100c1c4808a0342d0b03903413041d1400480c1d44890001d41c1c00814060040000c14441048180d0452034020307041959091300364104001580d05840001d0000300502035008491080c0b24480e000500a0a1941494454505918450003100d0404c040000400c4480d9501d8205040c0e50000401c401e8030b201c00c0c1c2c000003801d007400d8494580540141c0d4005800c114041c4558400c14000c2e0300c1d09010b8003944d9aa03400c0f01d40072441c81950201c014040440309949041829100f00060748071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 502144667 1250 502143417 502143431
    0x308010905060607021e0607021c1e05030712051e0d06050f09130c0b030a05040201030e0606030703020105030408070506010b070317130602030907052d040e0309091005090a 76
    0x40c91007a200c000b040940104400c100c4540180c989501402c405510035028003c42503a603000100e50348076101001e0341c0311481d40090030b400100c800e02180010b2091900d400b4054292010840071621820054407641050080c8804194520454403091803946001881c1001644034108000880101c110860201050141900c8000c0c4200409040125446002081d880000602501c0c00402550000030003900c8001049110303034990000d403d507481550b8807443c241c00000000c04084400340c1c00242004840540c0c1c8001150540c050300c000ba0203040f5440c1141c005407199803018208680601f02040540d01040051141c18003904401c58556034448a5060041580242d4440c00310004684420302c41122550115940ba45078058009a200d80c1e445040608007a0294495904000c01d00c0c210b03000b1001c3c42c1e0110310010040000005040c0360700003400300300e440c070070301c0c55001c1c2e0310412101c0510700e400030b1030766402010f500c0060100c40c0c8550100719040800c3d5120701e450707521012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 502145917 1250 502144667 502144679
    0x171c08180a080a0e031e1f06080a030804050d11060601030b011103030f160f0f0c060207020a0e100807050907202401090b090406110d1811060c280f030801 68
    0x31500800c081d81d510702c1d2200c40c44003e61a07451f100803038402480c408444080c5006442c050704080300404440003550300f489c1a41c10b002d4030042046504a9290080d03001f0022054003840902c1190300c00603008001e555290700041d0000c1502d124503074180081b00d0300c043c0b0f203a102040258032030709200030700c4045401c20000c44440500014601402c0c010201482790700c445c0d010314103413503415071483e052005082078204540244140701c006504a1000e00002c51708054892050f070080ea50383ca0f241e0003a6a03685211502d500150042e01d41c040100340204100341c2c45010428210000099050310715a2017403021440d01400003843da010300301980303003070f82e8140302007a40d5401068102d806000c0c68005a0004030185401040108200c0d0307542c01802182c03049000341ca071240306201040100761385010201d0701036507a12074111240c2c03440750212000c50802000780c50341146130a00030701c0b118541d1804007000701c00e00e0a8000c161211404280041018901c400480718020b445074101541052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 502147167 1250 502145917 502145923
    0x60b0a0501080c07021507060f0b10030c0909050408091e010e010c110d0528020301230109181208041109090a0822171c08180a080a0e03 60
    0x80e01907814000e50340b0030000428401d80132139480581c1201e40d44501054500c0303483d424002c1c0703280500072610b0710b44420350719105a481825103000441e0515038910610904805584040c15400006000d078401005016003507002307160003601c00c04002d400c0214410210b1900307140400c3c0c102005080707600f41001b80d600503100c1c2124003000c0c42c003a90031030017944940c0b410141031040c15002c0d400704d14580040c014103000070380c4291498184071140880c000b880300c50920041c00e09070310070351800681408070030407029500c4c403081d1400110026030f840e144010004240007002d03400f809503490480310001d010404150300600141d110400740d4101410480b080b03038020102c040c087c0b180d001c03c0c0b010034031000400c49162a8011400f980c3d0b41100060610043c10405c148421508803074070105020141460112400315001e0071100e46401c4a1030440d2445c0b031051902c2c010541c1d68000c51000b0705641b6401d1024038490307048544060b076a945c0c1ca0540c4d84801c9840303002680061210301d86160034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 502148417 1250 502147167 502147169
    0x120f04120b15010c120c0f0203030c0d090f06020c010c0804080102030a140901050408090f0d0501110403171602040e030c1e0106080309031005180727021e030601140403060b0a 77
    0x4e1038280142c0c42c10741d40d0901903110410b04981400b060b840210b081246500007000c649501400356901e070500032200d650b45490000c1c41e8408220124004503440c600080324008a450503401480300c0c070b541e4001529040401712040d20603060421000c0b0300c44030240001c5014041c14200041d062540f24841241d044000e030800405034105418080807415000035144611404c85202c0b46103000c04000540ac04a03500008059500f007052039031141000702d0240c81100d00031100c60000d0f02c00074140c0e002c144150060140c44000000940025040580c0607070901103240c4205c038907000310f0f070f4400c0340340018641903418102c10240b0412410300302801001c0c01000301e90002c505000340303d40003c1d00d03028005d2000780c81ca5036500c0062003011140e01c1c0c01a90f040c11b42c05031120b058940c02d00100c00151459000d014600f00400480d24003804d200b103c8a20090390b44807a9001000f0f41c141d249075001810007810480c07446035101c4042515002800110312500c40040c001001c5410300c83c645c505 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 502149667 1250 502148417 502148419
    0x1080703090308010905100e0f18070608151513050f0f0607020d0c03140102030a140114040504051c120f0203041a06211e0c0102120f04120b15 63
    0xd0001050029070041449815511885408034150b95480c0d07c8420051442c1c2c069401c21710b4420500918181c5641010b00031a00c0292500284103406c404664132040c0d48108030003e180301001910304400300c082c1c4d105458004205252807004001d840a203a04100d2a80d084191030442c200039904d0800c21048010300240c8103641ea40c000000066002e006000e1302901540048500c0401c1160402e1120301442d4080060f201c0042d42e24405030003500101ca9901145281ca400010800000c42006040360b007280c2c00c0c94a01d20026091001504000c0c0040b147c0b4030403101289140e0344081d400200919195403001110420130941c07c0549501d0440703800068810020300000c21411300d400c0e034103980700e8030303100081c2d48521001c41d600041444120f034001c2c020741080c00005101150b41c491540081700d050140c078048898035238036201c420000501503407100301c0c03460189000c03c5c0503144422244600350300301a0f0351080c500840c4400c10007143d4020501e81008203100c0e940c1008004060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 502150917 1250 502149667 502149671
    0x23070201060609210506090a3f020a02101101050a060f0b0c0f0607110610060815040b060301030305070b0906101202130f021830030403051b01080703 66
    0x124002001c0d06041c100d004009009540c2109103494583c00344c030001c41e107580b010807a10586400d08120307490305180708045a808486400d00c0e0b0551180c80c640c4400d00c6590001100d0a50866a040080320100415a0103601424040b40d01507582c0318001c460708159902c1e0040500344a52020f8215400184804803445c5001d605010004401a030a0296031803064401d940e003080311540c3d460b003109410b0048041c400c0508229020fa803010b100800e60b0883c0741210320b25140c01450071035124990080b03500188480b000145c0e41011000103060510b0081d03c005071041500740802c000d58026001038021440c0040d01c2c5041100c450748040c5e20122040c00791100b410300d9050810320a40c2407040ca1081c80e40f0484000035561243d08003229520601010848240b030030807010040d410880c03a008061030783e090009810300340700d01700080c02203404191840c4984a8a071039201c3d40306080030721005200c00d200110001d801045400144203c4190080d030013159200010b00a26004018001f054 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 502152167 1250 502150917 502150919
    0x10f020c0712140102040b1b03090102060f100509092407050d0c14220603111b0c1804060b0a12120516080c0d050418050411042307020106 61
    0x340e0214952090354542d4280106241da00d0038044240e0400c000648002d500c00500000c0814188004107a5811042c1d80070750962440b40b08551640074a405c900d02580098000038012814004009e91240d4911402c0810548817004625026000c6403680181e0380b121000c0e1040001d04021981000c03811a4a0045c9250a942c01000f5000c0d840c12682c000340c44414602800340200646030a500e10f0301c0c1000d4680038007480c000c8115141a410300010300c6505404201300748640254107a43d29000c40540c540007160401c2a85840c4040303a2007810b004620300007500b90f81c0c1071440c021115007111a000d41d8181400d00038225505104000d205945440c000c105c00b00b1000d6500e240980c028040703014092540c4002c0e1221303c950340c070240000c52010000001c01195074091f007a060103007000c41b404c2d095041d0081c0c40c14171960144110b04040b031018031010451980082d0340c03182c4a14030199051480310082000e980700998192842800c424450443c99014050f06500c500d0610083c8825 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 502153417 1250 502152167 502152187
    0x2040918111005160f0204090809011106011a070f06090f06180b04030e040921020f19150f061706070c020901090b0105130b1b0304030818010c15020a02010f02 70
    0x5106180d03952502c030130080002000c0c4000d560412040c1900078005118501d014508456164402010540452005d40000c500782c0c03000504039050f10162291001901c50115641707940d40c2059078200c41c048564109000050b1a80c01000d07195489180c0d14101642640b40c041c0550f0f071400360920101c0384402012001c981a8002c581c1c0041d09410103100e03204410300854054001c8681c058854011260880c88040c081c031045000c1800c564252048054140461b82d01c8001c201d0a210748507106000001c0452a510600344450740c000300b00150200705400020140c5e0b00a9000310308410880489500840c01803000d2940580580382c000e04074440350340080c0d0b59000c10f0150441c03a69032111018000c6c0d008504940b42905d8503661106100d80d150045a46039000b207072220038051200c0c90034440c8000000c10345090700d5008a04038203180b031407025450700a1001c1051030401403681d80540c013181d030f04a003039400b00b85082c9026170745e0390512101900b5944060300d900d2006104010304054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 502154667 1250 502153417 502153427
    0xc1709030d031812020313080c0d0803091c09060f02010c120b01210b1503100b030628031209050a0311061306030606080606040303050a030906020409181110 69
    0x211660400042c94903001507001001c500c1d90000404000c65441d980131041e8000010300010401000c40505481d00c07280000e4480005d0122aa0000c82082e0742e40c00284140d40559030004010003121030400184195007401000000a0804252001818420650720201608804400740000d02654603500c00040509582c110103071f411558611043d24540e215010b1010710a041c5d2101402080c076640801c0300902e006020903202c1c480c2030580c2000700c041d12058030b12440412210355035091411500034419800241a158032031900c1c800c41d004480041d00001040c105602d43c055206d00b107243c402c5505402c4070240c000d00c11408020080f6503201d0078940300781c0c0d41c0450005000500c1c0404203040b4081d6503036a54520035013075400701d0b82e544e0640c1f0ec80d0807540d869540c66156107541060007440d00c904d02029001903000c200d1010441c0c00b81e040144002c0c42180c0041c0b03855625901e41084030342c052841400504070b140f86c50140510030541a002e20300840c2d62403010300d200f2002900c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 502155917 1250 502154667 502154683
    0x1514070503042d08030f01172a0d05010e070605180112140c0a0e0f09060d0201020f060c1c0b01081b0d0c09030b1503060621010c0c170903 61
    0x8001082503d641d0f584185400c0c0340200011400c01c6400641803411002c40d80080390700d4810300c001000001080e80c0c0440c111411030100f0720203840140d0342d8403411884003214486641003245045810b40e06900c424003100c802d280102d00000311190100d4405040418552000007042411b1151414a04010000000c942001d08142c4210140300c11460080c011521408030404019030400541c1c1000600421954055646400003401000200202c1c080e00d5000550013881440002e541400c000b04c0c80c040f1540140111540440002c41b05850b140c000c03198003100810124007041903c16809240c40001003d802c14000c641e00c0100080000c08001e00ca80496a40c05141940703180d45403040b60080100300e542404040510607004d40741d089113110849003001400001030407140c46002d484013106009010700825144d060400c4003234a031501040c0552004c441d02d0610a0300d007440b5200458802c0c0d101c42804240b9810010b510702c40707088410032520000c12528055030b0b80454204 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 502157167 1250 502155917 502155923
    0xf07210f1218080901080c0f0315010c050d02030904180503030c0f130b13060c050703020909010e0102070b0708010f081207030c0609200d080904021b0604151407050304 74
    0xd41d0011003140004040e080c00441d41c50482c0541c1c1d511000e1194800060861072000c3c6c03500584c076210410f11104030f20422000303502c0c450050011402d0101d134000b074400c0308032051410955032101c9454190a0400444892002d640001046400360900d802200803181d8082c0e20010a00695100c5580300c1c44010102c440e0b06c00006113034280340d01c2000649034100b15030b5001c802c80c241c0b41d2290b14456400705e601010590080000018500e10031116140c015600c000540300903481c6500b40000c0d8600070f4020001035403070b9075200a01c40c00900c083c00145010b0880504542032091000d0800c1c01c060708030130358480c592072051040c0c1c04001400c40130074404095079555501282002ca85601c14040d004090604101c1803009012201c002021054100500c0e003031210145001c10140c1000d00100402c020420b008000b0b40b454168054983c6003506202000600f03c001e610710304105040740d00b102c0a10511819202c105032601c11420001040047c603003003824608030280885c00018401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 502158273 1106 502157167 502157177
    0x1008060f0a0b040506330706140906070f080912030a0515100c080904020712080103030201050c130e07090f0807140306060904020904080702060f07210f 67
    0x50203840d001b000002400d018442d1018452800f000342100c4a03251605400140f01d0380004040007403140700001804080c2c550001140d403c00b5040c2403081c2e01c0724040004054001c9643e0344038015a0601c000740d580c039070043e5841c0000740000158586808020b1010074402600302502411660840400906c0360201703126807003a210440c00005941c0c00380c10004a002030000b000441d202400c050321b000216100d01000e40d881203000000102c000c001041403546c280700782600240c03494000c0c0d02c0c0401d04052514481510301458682c44004c3d400f298640740502c2c0c80c01c0081c400354011860940c1d444410588480712841003c9624002c41e0021102d8034000c6202032180c100142104034548803a028094111401001246da01804001c0480940d4402020f81400012140d02d2030b43c80025184c200e82d1114004461115424140c1e1204040b5030041c0d1001344440852030710f = true := by decide +kernel

theorem cover : BRFrame.Cov 501978417 502158273 := by
  have h0 := BRFrame.cov_init 501978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 501978417 ≤ n) (h2 : n < 502158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
