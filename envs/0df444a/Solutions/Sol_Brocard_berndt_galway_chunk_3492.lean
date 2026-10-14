-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3492
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:49:08.196228+00:00
-- url     : https://prove2.me/submissions/7718db3a-4448-42fe-baad-e15bb467a722

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 627877697 ≤ n < 628057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 627878947 1250 627877697 627877709
    0x6140a0b01261302060904020708070b070c020d03031a18061c0b0406020c0a060f060f08061e06010c0f0605011403160b0307091511010f0608070302060915030c040e0a06 74
    0x80b0030001003480300b401c1c0c610110244003e000301e1904241c40002022604184410340b45c1840220700301c0d041051140780c0c603030440b000341840d800c24542503000480c0320300403180c01000c143d2103814104c441d0311026a00c0325a500d004046207c0c11400c10440000c40c801117901c01d00c6106100803260400c45900d44900600d0303041000d014031380e071b00c036100c000195010f08115201449410304850200e40da500c40e158003c3c401e550301180b81c070f140040007070311411940c000030080d420075000d121540d1005803100c24114104440c907901541e4038801a03a59101c0e908001d4100c0359100c010404000c9240d05c0203040e209404080480210507005040e514070b44003441c2c3d2080d0862001c20700ca05421f0401655114402d1b140030311455444440714110b419002c6440404a00700c000f441400c001d080c001e042070721503c0101041a185003a158a684201600c400b0380500d60000c2d201040d611581918000d4084401e0f280b81e482c2004425401254080d201c0d0f19515000c01012440b61055070140800701e40f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 627880197 1250 627878947 627879017
    0x30d2c0105040b0a0504050613140f060306190b0c011b090b071709060d09030e0906030a02130204150908010e0a08040308160b070f0305100501080c0706140a0b01 71
    0xf041111000e9141c0c80882611305000c403c0c4000201030765810024041b514a1061100c0894035001602058a0080040c0c130b00c5a000d5109180b0561503a80940f5440f8604554250007500220160641240c0503001840050360000341e05d0b12010341504202c0d01c040d841c0003105103e0340300c10320440d82c0400384c0c0035010b845d05003004060082440007480407a0451a45900d0303160030b4404d000160b10341c0c020b88414200d40d0f01c3c5c0d40b41c4410716402086071218030a090310400d040349008000203481d1300311030340000c0c03040b206440e00030400311199041c2d4001d0400440b4203c003401814501400400d41881884404c2d800e054003c003036048003090301c0900702d900282c00c504007400d51307507a484030790041000c0d1144500031101da4000305106140e5540159421f454080c03c11504a0004040d524010b1000000b1684404200080c0e603020132040c0c0e01c001c15444040c0c440d615403420b480a4045004e0411007540320400b03001c5581481c1c0c2c04101c0c80301c0c09880e080b82c0000c10b42445070142c07500e15440c41c8448 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 627881447 1250 627880197 627880199
    0x80f01030c0605030a110415020c0a03050607140c0102070f021f080109020906190e0f0616170706060305031207110a030509042c06010501050c2a030d2c010504 70
    0x1e010343c0180d80c1044640700003054034402441001c0780c80c1c2260780608024810501201d20081e01405175001d244001e0300d42445d00d90450f1681503480300701401751000c0102441c0c400c0d40710001d8030195444411040001e40d541c408a0900d482d685018800a074805c7c508400d80321201e0b0100188030240c00b110b034071405481d03884d005d5031303030000e4220000300c6401680410007184404155a5240502621521031a0780149002c041c44500010369104c54011042009802c0c002c52015001c0480c0c00d510808107418071410241d0b01000e03000710301c2c00410160134414048200710001c40a40a00d04004004c41c20326a5916000c23501050301404050f0701350040c1c0a29400720b485080200901540600701042c141304080b0a03c0100006103a00d080c0703000da12540500812040c807032140140000d1914a003030141c0c18040035240c1c007440383c0c1400e0081551a1020401a10178800ca11840c0014150384960340400c0c0c01400c0399070600419a00010003000c000141c62002c603d070121280c06a458500381 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 627882697 1250 627881447 627881459
    0x6140709030303050c12250203090f04050c070506010f06021501141203040f06050c0c010822060902060d090201090e011404151a040306050a09080910110d020d080f01030c 75
    0x4040240c00004175071030401640103010b01e0782800707900a401021142c040c4105503080011004440c0e00c403001150400c0019004e00e41e10340c007078080008011240016962214058a58a4071a0700e00040007400f5000002411100d80c0705241c0841d00d0725001d1356a101038035080d010507400240582d4620420030782c94403c2c1420510072817284d24614500b16441c0603211034000c0001d40705d586c4400001100041c039030700d91000500815405000c00c0c20501c50324201000900c042408408002150201c0000c600081c80380e20303040600304940107410147d4038030202d4400005000102000d034003042c0d0450300007c0c84000007080718126201c1d000300c0240006890b0804c0013608010340c1d4403902c80070a180100c2d000300044132030b80040320030300f200319a564954541802921002410b8040061800c100368021030801403c0b03c21040c0c0884142e01308220034542514001b401c603403024040c1c0324202d0a00c400c282c002490300300b2072074039440d01542e0ba07a41d09001505d40109000080890250440801c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 627883947 1250 627882697 627882701
    0x9030206100f1a0d09050f010c0e0904030e2806050406030b10021207050109020a0b030609010e0c0702011b12030e010e0f0d030b15070f15051b09030a0b010b0706140709030303 77
    0x4d0702c101000080b449801c19252035180400c070700b03c083c585075503401c0d180d03016a812040700603061405a60104d260b161a440203032a03a940c05d0f05881c003c2c546451486c00180360405011942503048480c82c42664441000030000e400601466020901d450802103080c500340490548901d0075030300a080c21880c00c0365141d4203030021134040f59950340701c2000d0310059071a078243c0009401e90008107503c1c2d140100401103c0001030f4444000c411000090081e5a0400c0c401c4504064080c2003424850204a005001d490140304000e00202008548811100e074142c03c11440e20482d080280810b2003c2c0c9030030703a119404000f1441043c0e0020300000304980c025006100f4414001304000ca4049d444440c4801d40c1d4015002100c0d5074550101213000c204194601c01d0000c81060800c001c11300d059506007000e039013200710b41c0d0030194003c981e030f03a9669410031030381104662040d84120656035451010342c064000d41011110036042c00300343d025001e02801c6c1c80744185216521201d5a514548087d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 627885197 1250 627883947 627883957
    0xe1005310905090c01021e0a0206072108090c01020f100b180406020a090e070e30100b0f0a090e0307020409081e03010b0708090301060909030206100f1a 67
    0x21914455000c0000e50003054800c0c24460f07102500035000854034403000a05020280403082d83c8035905030700d44804403000046001c0d80c5541900c0103507880502c0d003850206d100741c5180c1c0908642c10480310301c0c82290b004419074000d00740d031400c81700044501c0c0c00698448560380c083c48031550140307a0060700c10469070000402c0301c01c082c11581003000c0201c3c2161205100b01c900792001500000c2d0594406e44c4501d030000104921481481d0303d040040004104440b0403040501c6090700c040c80c4607040c0030700380f695021003030310b02001e0307040030300081308552100b402c070400a40051030070305542d80e41e0908407421515120000c220000c0241401681401030070081a017905501c03090141c8070041e16184681480b80b8002c009840c1c136650541c540f080d03050741c0910001c05a100074001003056401c00c2c0300307482419600c00c2032a5100d081c114003003030050000b6405080803a080000710401e06401040060041c90b40c0da50903030300d40e5250410207082c01c030248601d0ba07407585210300f40845549020080c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 627886447 1250 627885197 627885277
    0x914060a110a081005062d0909070305070207050a06110106080f1c0e0301050406050a0f062402010e0a1b060c050a022215050a050906090f0403021c0e1005 68
    0x5130b22903031a0f401007421354100031074030b8614404c1d401401689000003020100040da014108601d00101000402d005500c080c241c60245034840e004916010700034407100002c0c104c06080c20500030350301c0000030b10b200480100000700b0352030701c0340101c1e40100109901080e00703150802410f2032200740040e16a4402e080d1154420810799464004556500317009103401140209808074071810700c000303480c04841142450380c40e01d603e130207004c0001c07032844110840340668643c0a08115041c044c8140d02501c00241c09131080d000c2d042c5c0060401c0580403506500d40481d00c4210030a58030345030103640c1000c050402820700d51002119a005180144401402e910340180100701c45030358031108e000340e600c160b580501180440c601448a4100080130000510301107448035003034240b81d804030783d030313110007810941c160b403203c0c800503040c0f5008105500d01e101c3c1204004069410103a801070001100c021500d01c900d903200c11001a050ac0380c01558030a40b845030005150b51903482012181c4050710b5062 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 627887697 1250 627886447 627886471
    0x4030506060d141203070e0105030601090513090b0103050d021e030f03070314190b030a080f130e0f060405180d0e0f13091101050403080d1a040914060a110a08 70
    0x5036094480c14004000f001c028203070403070344a046c6101d0291100e0291a00d45042250500070003400341c0c0d2100ca04000c842059a0170701010f49003501c5c04014044145001d00142c3c7d21500000800c0300014001800480301c2e400d0b00ea151fa402d050300c1d44d0b0241c01014103007956100b803060302030003244c0000454203c040c1c0e040000e9503403201ca00d4a145010101d400d40c40105040d079403000541c2c80c4c0e004200b4a003004901510025000380e5442c811806071510103480e43d00049035140d02d04e075035115244081e00ca00400d8030b116140807642380788911401c9800074021813f200205120b83d450304003880718000800050b107080720200304110f945243c143d8a15600c00f05440235000359490301c80340502c03c0380c40403401060b52581ca08100c0c16035044450300f9030422000700020004545210141c030052186101c0211b405488a120704240062407196641d00c01d2030003004008000b0001c2064500803201000c0d81d07060750301c200d40304046500c04000802e43c4002006020055846181015440000c03c00e01e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 627888947 1250 627887697 627887723
    0xf060e0123120604030909020c101503020411041707060c031d0603090d031503120f03090c090506120a0c09090c090f05100906060c030503180d020d030f0204030506060d 74
    0x2c1c0e0084030710402c03264a41100c8244001d06520049900c0a458085802d504e001c20041419a4440c4e0b41a0364500c01c0b983e4024030b08051140303840c645c00854006106010414000150341aa45c2c003038400c1003c8842030000003403000202180040850700c0d15144c184c4030a446032001c4e01d0405000c0110000911702841c41480d03556107102560046070b803040103001c0d5200e03004d0040e08444070741e80a81c410f40240c00c2d0400c0001c40748540f110b85041c003840c0caa0320b070088c052070540c0035140298000b07000c41480d03580407600400503070095102c2c82080741c84401c1d101d1400c0c0100e880c0e801102000e040728070216028001504150400e50f0550320841d00000c603d55141e07000d90403a0901d51a90120365152000d004080c1d540c5500d410191110007401c00c0010301c3d00b1b0000d011401c3d0398900905100001c00000d5001c5241a038205041401c0c10941d0fa0229612030001d489424092031417001c01d01d402030b44004001d0724030070380b001c0d243d20000500300780d20f5000c01c2116045039090116100c0c0081a9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 627890197 1250 627888947 627888949
    0x180a03050d09020f100f0f080c0901030225060b04060e070c110a27050705130918050d1101050109021c0209041503030906020d050a02060f040201140c0a060f060e0123 73
    0xc3c5c0001c1082156079890b00002980c100516001800002da0300704085e050030310100c50100421500341800900780141c1c0d0300c0f008886500b00c24041007840c4041003100d00d03984144160354220028150088404101017501da900c0c0407100c5034181c3d50b40e000034160710041030010b00740507141041800d004155a91159691400b10001e140c0301c40d031005040c8032841700c0a00b94503d4012a0740005241c107225060032084000040710f54802d00c40c104560703444699074250080401081e0310166002001d95505c1080c2c468040c1031b1180701030161285600c3c060002440020520a51710075200f1800041150f4041e080448c01a4000d950095409942da401c11a42c0313068014811005510984440c1b01e00c40c81c00d00043d0421124204203802c0c4103040003030540c0981c0c00f00300c0540c044440000e02580b07850360b00040341e90045861407280c4002e00080c4a04400e40000f884100a6228440c140403054402001000340c5a091141500c00e606502c01484408000403d010700c007032000d41c024407060f04101c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 627891447 1250 627890197 627890209
    0x1020f0406050c0106081519140717100612050402040609090f050c1008160e06131a070825050102160210020601212108180a03050d09020f 61
    0x81d20900104100040441c5018020b00aa0380100280006051042141d4a195444100c004c002c500d090744031405d0580c040000e5030180034550f01e911207a200c50301c0d250380040e00b0000c030b9403900c506901c0d00500013881c440c284207088040e0f44895640c8480d43e0380c0d89807554043d102c06803080740d125459074400303c0c0940241c0705041d070581c0540000b13043d024060601905000d4010229070081310350702c1122030410f07085440c0c20340000031103614200050154508640b01803044800590084c0000f070a40403600f8084202415540c801d030b241007000ca510a280c180710f10816100401a0300207004030f4881c1e1000c5000100914180318401080701195501e02d402ca0340020521001168a00e88003801e504013080035090040b03090004001d2541000c000c4607191075401070208407507200180c01806c10410640440509100c0d0300b4440c61030001c0e980c09003804104840d1090086009216078122507400a94240103e405480c2d16140c41c020302c26140c0174010707144040e44c0203540d8202040315902d0b85 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 627892697 1250 627891447 627891449
    0x714010c0c030801080a0c03111215090f03120718120614130b010b16021f022506080a06030506070207050f030111040e04020319030206041a010e130501020f04 70
    0x40c1e92480d141c0c0e00c6618000c3c1007020103800c5a0801c0e44201170810024440300802000c1d260441c0d024085100c0c10000960700c8801d900d00310410b4003a0f28034202c061145401d9460103108000295048110501d0350142d49002e54400c400d00400c145001c02d641c1c5010300c900000340e604000b5120a0a0703280c442151550320040350807251540e6481d400d0003d603c000310610342003c401740781103d84005540b41d0700c06c07122041c001e40608450001d0007a408104c100801e00c61a580a8a990340390401c900c034245c1c0d030b400d00d0900d90015004209403481c170000640d1458039415000d0f030002404900707000c812034503203200401480c01c0c0307503990f20b0200c0801c5007001690f20444c0203078001d2031820304140030303c41000f40901d12680039a040c404400700c1d07039000109480c1610030425140b8100c0d035985c00001e25000308482d2454045807030000940030705a02150480c4200d0161090401c1940c131902080d690f108244543c0003207008030f0002c115034555070400d0b411190b004030000f5041444080c00e4070829401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 627893947 1250 627892697 627892721
    0x30a0203040e0109050903090118090e060f07080f1f03150b010e0126060a030816060e0a03270305010204091a040504080912030c060c0a02011817071401 67
    0x801c0401064900c00c00031405050007060070b210508180c55281d5480c014000007505010b01029111003401c10880458007c1400c0c0c401801200081050f41c1c0d141c0d40d080e240454614040000510114046e46040c4d010303004c2000312140321790b90f600060031501580c0035a00c140c0d2182e01300c000046850310ba901a880d0880240014404004000240400c801d40240c14140a0741c19a00286258030483c101003003061644c4010081d5900380c000307501c0107225040244840c001088280d0702288004110b590f00e4815042040003241a90300140c3e01c0301d0065000380040d02043d00c00c816810881302003603901d1405030013401050344a554640c2603070883d03000440e6455a5043c0c001070080380030003036490f44070185e6041060b4101615124160b2182c0b80e03a190180c044400d80f00b82004040003200e00b2900510203580700c50400184510066000284203001517080c0049030303000003080c8004460180c1c0c4a04100810b030303d8000d17122a0340c0c10008064031840c8040d0291400404c0a000d02003040503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 627895197 1250 627893947 627893953
    0xa05120a05120d1515110c0402040801020310090e0d0e010e04050106020c0a12260408060405010605130209010e0907120e07150203030c0306010509060d1a1318080703020708030a02 79
    0x20605042a04607a4a4011103d842c4c2e0005803c00001380764984111006005142c420100803480418901d0a01d828550640192001030700162028040d4091401600c0a545203921180e44078404416a2200c2c1c1c0403c003d5004100b00714900c40c062111340d13003514418140003e440441d10001030031513800b64030410258001d13645400362440d100e80c51002812080081060708c110603142c2400c3c8090729181011014080051120b5400401090705d004102c82c500f224010300c0e040c6040741c0600384a00c20103010300030423003010006000700d00075a0341010060b59804480d51402c4108101114003410403424400010740b8402c0607100c41c005d0f00d01c10801c000061003c1840d00e201d89603215011402d03402150000d00600450558500490b40c2002c802d10300251900c2d5100b000a549104558108040515068184001d000350b1114006100401c90301102c14024041c540d45c1079a903145d4a9220000c2e400e80c2e5000014050340240c6445c4e8004c5c41190342c8180c448140600d03645c00545080c01581c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 627896447 1250 627895197 627895207
    0x612060509010b101b050309030a03050a02070f0b03060108040311070801021c02070302071715190b1f030509010908030403170604090201050f1e0a090e10050a05120a0512 75
    0x81c4090003040b800b450300365030403503c3c0036000c00c0007000c07101e800c0c6058000800541404042c050100180d480c020001015281d4280070351030301404c0e039030011282c0f03805401110300001e484e441482d000c00480340496500c1d8619a0707120011a45990010b01c1107091004081c036900580008100b00005040e9000c00140e8602d1016181d140940e04c0c43c49102c00a0300400a180c00a0350110f490070440f0082c001078415526410356181c10a901d02c8610740d0010200e0041049482ca620045c40740300c85440420408403c2841c00c1c460301d140303030b10301e481c859990400c074541c0c4040c8a80e03c49070b4450041c4000090a014a5460100039802a07400340c00141014411844141e050703e40c40d0b0300003034215400c000c0c283c810750000e4201d00400c0001c04035070001080d0058500c0d130410720b09035002d0b55884640d50710045544d0117003072002e0703901407a16000c2d8407500290b911004c6083e100180e0700c00821040c1d0407441d010820500f030f00c1e0461050001d0013805001000078408201c91020703507043c84002070303d0b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 627897697 1250 627896447 627896461
    0x503150d060222140d08070f0501020a030c0e031b100504090507030507110114040605060d06110a02010f0522051207060f0b030307020906131e02070302151501030b0406120605 77
    0xc6412038010380200c2100380744e000940e42d141c644854006512640007600c45050b424500044413264801820650000440d441034650642c1300d20003150080c0c441d913203891580e0051507a5440c06138516190542e4190300c82c58646442c0c503004d500c052452920740c1c0341503210b82c7d48000351401070790910046a21074060101070f54104a44003004000071000704140008035803080b0060034080c0000c0c0280780d8540104525848140c1d05802c1c03a40c03c02000e00084074804210b000030703405000010019440e0249441d200703a514082c182c0100e0380308841b28803441700c0d46403190720212800c4049800740b0502c1015050b1004001c05884168014400025080041c45100040c1c8140c594400d10070b400800081c030040e0743d44421290002d1041c0ea10180381341000c0c2001d001840c0d842400c1d0911700c440649969400c03200e400401100d17200e5403d0b039880d485070078a0310390b501c82c2c2903d10017800024400300541e2544a41d1107a00582c40c0200301040071640c41c030305640e400101c0d02068486c10344840421800e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 627898947 1250 627897697 627897757
    0x7081612391b03020706080601030b0904030c0213090309050f010c140f1b011704050708070b03100501080402010c0f030509041b090527090a05150103120f0503150d0602 74
    0x3a42e490807141c4440707109990003034a503062070090009005406010401da43d110b58070040c41104007402c071250506090034094a5052551403c03803043c86494560130100c0300c903008005c40d007a49612039013141d500b05820407404243c900100360402c1800b11064010941c664401c0b001805400301170850842c4500d0920b081148400000318840040003114656907070040310100d9840c00f2400308030b8943c840b4603100d810301c40b00342e0000c0c040d0f2058090224001400d5001075010300a11843c9001603540c403001075612030801c0710083d000c28105e49144e0003042e0155180703190369201b03141c0301d4035145460b000030f01141c542c217048140c13524044004c0013909400110900c00307040212a440412b403500302180d1011004800b403511401a54400320f4400d24081202802d0150b001040e41d0b041c0c1e0060a028655100901c02540d1480442052082e0240120001032070011660340d03042ca550340d64041141070b00322021a690b00b00d1034512a80740803500300d10180142600c5599450050300e200900641 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 627900197 1250 627898947 627898967
    0x90f230304061707020705120312091501060804060222090e121602040f0c0c0b10060f030504050a0203060103140d091d060a1d0708161239 61
    0x442588204030500c11603030480440f01c40b19614200501c07180c2d480080403800d22800354010f6421404645521145400c040060f1804200c0448041904c0e503690301d0391a51040e401c425203000111000061100902c506a01940a4001c40001d031034400a05500030007001c204100100b0005074440c1803008803002d025044290181d030380202211f0358524140155032181c0403000d059039000801d0382085403100e8200c5520009014010003c95039042e10150981c9030380d040031a4250404e03400202d0481d0440100016507505540340c0c41c0c80c8103a00b0b002d400408001d030007551188a6003a000c401644c0811415010754424580c4c1d04024044001d81880c15152564000c11300034606c41c180007500712544160a060842c0b03084081640310613000c201a60300b01d4202c0d18519100708404000d5401258041340550220354072058241e5607055040f8000411081e10000200030011160790042c40da000b50803148142200c4050840c81e0424100c40031041c080396200d90281851110040c6030801c420007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 627901447 1250 627900197 627900263
    0x10201020a0e0906030a050610050a120302061f03080a0c1e0206070615080d020c03070902030402061903060503010221280e07120b16180605030901090f 67
    0x541030410094014000880e800c485500030b009410000302259806c0102c500025042402d0f50340c035042c012010001c040c030a0203500e002d0602c1c0040064060150f5000510b901d406501501440d225130001c081c08450344c0707161001c030809002020010a001e0401130160004e00e4403108031076146840d1451580d0200f00360f01125201060031400580c031103004842c0520344c040700000300c1351022814400252480c0c1c0000c03010303200701651000e8142d0001941844088114101c0365041d580b42541403d03403004030740080d0064014480c1c40c85400a034171840a0308a0681804610300384c9860202e8226045a0020812002e25036444401d601d0303c2c08290341c10190110138040c0804c1c604040c40416511441c0040007541d80b5100c5691410081c04020080c1c0314484090010405c81e0515081d0040107890f1742420a00c030076a1204014040e14904110411007551000348a18001064600b9040100022001d54a03070300c10a0000c2c883c0c14825605500c101024518440a0003054803105000c40382d507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 627902697 1250 627901447 627901451
    0xd02040b07021e010504031401060806100e16091203030f0c18050a0501080c0a211e0c02120d0f3e040e041b1502010b0105071e170c100b010201 63
    0x860296617004003200d003601c2c0c0203924041a00213190000d40140310560000c0300ea800781c54244210386a0b41e9250008803441e844146285455182003201c4058180c409a40803d00904041102d013502c01d500240e014024180085c4002603243c128040d81c1c14611048000780c46601c04280b01202400340d03a02801c429070f144510302d4200000a001c482c1c000d0211140ba0781c000c150303054514481d074414100e0050f07000300d00c980c4824004003400540071929420b020302c03220300304140003003c442c132540c0340900c8198001c240c819080149801a6800040107402c0540c49198003d14501d280c0181c40e040180c0300c0903001d1440b0381c403803e844100300d114200c1c025103e0507011440045100700658040d9200d00c1c0d544501d503120381c038100700307a603401000d10060100c00c4180082c081c02c0140883e6003540c0181c000f07110041031040119203900ca000700040005103c3c03440b401d205201c101c81024101c0c07243c011450700d10301103401c085543e003200e00214280d602c06004451450304d01e0041800800080c002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 627903947 1250 627902697 627902749
    0xc031905030702011110020f0a080f060a091a06030c0405040b0d2d0b09010506120309090a050705041a0406031d031615090c050f010f0503010e0a020d02040b0702 71
    0x58281c0324030580c14040e04000c912142c075030701d910b0288422802e0820104045543d40c040182c04e020b1070308002c1189000c12b140a00145205241084062084100414138004682003040480080640c0180d0620110f0303280400d184988a80000b50b02030800040c0c0d40f0348443c60041004196221003802d240208040c6050304000380521544d40003080301e8066500a240345a00c400c110a4a0300c08040c4c0000c1c0c9800500c654040306500440c0907a0082e5110304000f250360b01a03907130368130448101c0c0d908902071400060801d116680700981260441c5030407407519650f0400301c40794540240034000c0722800001c01b08507003501440b860340481100260120407003010703100039880e1b00400c00d0020a094000010208100d244003c901d04001c00b4581008601e0b0242086800418103006141c001c00780c00c0b444c91119030154801c61b01840c4a50385e841c0c42e50303090541e107850700d4201410f20921180c081c012440d1001c2103001500140441404a5886404900406c94001b000c2d03803021180c2001500e07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 627905197 1250 627903947 627903953
    0x7080303010b0c0a060c05070510020906071401150e0a060e040804060c02211e19030f020307051507031d0613081207020a0210050405010c032d020c0319 67
    0x16039045940390031269032986081006141000c404100080880740303400e603100c45031500030015240090295044810322024002c8500c1244240000180d11150038400a0002150540b004444921071400829240c503101c8188800d0348868104102c810010000c00c40e001d03140e881880c1c01020220704202841c2000d8a8800040c8034501600007007080308000482503481700300640d20703014280f0350503901c2d0b660504079881c7c0b58079061510902c05100040c41070283c00d40082c03c040289034a0b040c1d8100001c0d2907406840c0389100e0740d010800d5000030300450000c40c005000141c40590a2815207925140041d401421500c0c1b851505031007841c0c0364031004052400181d801c0e48800000310b00709000040e07042900c0b65015480c10307a44850044030401160aa003c603d22410500c251203100c94500c000710241da80d4001e034051140060500182d01d40468459000b00e074002c16448031210312030940d075000d4004550000f800340056841440e4400c00b42c1401c005440c1c182c4030360184080c036403803035039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 627906447 1250 627905197 627905203
    0x30d180c080607112e0216050f010e0a0209010b091f02060103021002060f07032706020d1401140402030612060403110d0f09050f0103061503050f0c0a1707180b0d0e0708 74
    0x204a40c005140a040c017450a0f0245074100d0340800c0408400d10301d5996031307282565507005004920700b483d5003002c040b034404540009950b03001540c0103110003070a03030901c5144103ca406c84540720b54840c1101d00704219907040c084039090021881e80c003502081d8118014014081040c0070701404541c032503400c000302010702c01c1201d5005030b81840c0200b00c1c03940a80700050402910551a0b18015448040c0020445582d00a20089000c0003081c0841d044030740e024008420240b15454042c94100c3d04001140740076801035a200800400c40329440418002052034480121011804520404551200c4003010411500c0401e404d207005520a040f0000081200c0304510400307026804428201400c0e0f030080d002038002d00f0743c02e0030442c1c0e040c01d20f200090140000f40c4943c5c0c03078500c442000c82e00c3d030750f00d090440741050640d0300ca40c8030049042a00c400c805a0040407002000780c12507001c105040c10032086001070030807502244d110400d0500b450b00711050303905006407a40c480181004001008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 627907697 1250 627906447 627906493
    0x6140904060c141c1802030a030c05030708030114030106051f1110020a1d030a110108060d080301090606110a1212061d0109140108030d180c08060711 66
    0x11012400c00d003012400e95100b00040c16020b822030f4040b405049082d2501c0c525003910701c0581c401d1103406614030f0703003580da40070112010b500340c0c000c81e0307003240464058600050140d00c11401c82e0b01d0304013181c13a0f20345a50001c0c0c003c6040703460702440006035031409008441c0901030480f00403194156000d40e00143c0ba454624600078018500002d88010800703024550b5081042c2d80250b5403214509002000204d68244841d0b80000b1a90005560300b00014880c001650041003030692542d15401505d201c0b8000b010150b0000b00f0080c10300015072580c024500030080c0103003b05070b10342010700c094000b00d907001c5903105550109117281c0c00f00d0300349412200c0c0c040301801c02417100c0e140c0b045914064503003508200310f000001c028441c0c408001d150502d049682d55001040022590b442102e0b0505003072040c08199801448944c000d010643c0c004003d0342e0600d0074040c4d40d4010f0756104450030407145d10040103504650200036182c1e0304056281c141c1c0000d80e0250860100c2144045204550 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 627908947 1250 627907697 627907703
    0x30c0201200d0903050c0d0f110d081b07050f0304150819021b030309060105120114061207030506010b12060901120b0604020c06090717030c07050411040b0a03020403020406140904 79
    0x2202801401d0500610484180c484900b090728520a00c1d0080541885108c001034000a1088403075071440a00201d0724500d100b0340f03551404c02a4a681d18500700c4659199121120810708001440c0019410004682142103c0700950380369031400c00300c05100700c6445014414012070104000c000800d0003403481e078207402250010307140c4544000310401c003c0024104441ca100010078480000070000710681260001c441c01030044c00d90100603170a960480740c1c510100b1026402003211880d00d0241c0c20320004030101100d81440d0740b901c03078510300fa81c00c2e40090401c020006101c0c3e6900303040d140c1c16900c00d03415a01d808481d494158010940303400050064407614450340815041c0d6102d8045401b0403400300111082c0d41000301d000c5480e810309106000070582d002d202d01e5444500402510135810014024041c80b92800c401e000281c800340c019002241c00030000411140c6801c0045c02890210b070380c0058a49080d0b10510085840a03003101d051080c00b5803c1c82d03805d540304c0d07015950040e8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 627910197 1250 627908947 627908951
    0x625030815060f070b090705091302131407112104091107050a080a030204090e1f27140708160609030c0501050c0a05071401030501090c140c0705040903030c0201200d 73
    0x281c2c9001103418802e17075421031a031002780e03013083c081049180c0c00365010044c021245044859448060902210604c8410b000140d400342e00080015000e404100f034181d00341410340301e0000c064444480300130203071040c181040d600820b050120404074800c01000100d5034140f2841c1c90303059100c4a540c1d448051004024400c00120100201e1290301514000e00182d04140451280345000c142c4448246606840c001d03c840c1d0140c107a110103004103100c0c4030101c43c0318488102c0000c03a0123094000008241d5080180b001c842030002d1080110301d00516800b0094208400c1d001c50950040c3e00c6035000404101e1101801e00108000b0106403080312000d00b00182c0d03401c5115226401c0080822018180307010340007000560410075000740100c40310903a0308001e01d80c0c03a6103510040360380944400000652a1200451a803902c000901540c60b105044070141c0e5a5240000d0645441200450009855243c500c5610b9024002d5221441003010480340851110320071114500a0001c8440d00b15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 627911447 1250 627910197 627910201
    0xf071502073204061802090f120106030302070e04050c04020a120c050301060e0a14010e012c0901211203090204020d06050f0d0305090625030815060f070b 68
    0xa4000c0092100404010031100c0301e8402c2c6441d8503245001409004410740d00c4050b410324140752034801d20083d40d901c6450442c1203800703080d0007802900201101c40e00032114080e00c0d6080d6aa09050b480d2100c410b10002c1500c07800c1d0b2500900305801c81e0300c07401807070a01a05020000b4804208003c180201f80c0f001a00c4a406d00c4c0110b8107045800030f8071214518200450a403aa404070085060301c1039038a41c10030780384561042c803219a4651182d00740c0b0f9000c0040780300941d8811052134014100514080d8280302c50700240041d00722014540700c1882480a0500d00d40c0e05281d45418014a01800f809400405800d84c402c006041403034000c0403540a09100c1d462580280d000c100c0c2150068400c548070f010005185000781001d00902e8031840040007981c1c00307480c00703000d00754640f0361607610319003054103003400c4c000550031075404410326070036001a03084100e12007004064006d01a90b10541705040642c0020030492062440500070f010403c200d00e1141c1c988400c40d58010f912192030b03036107a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 627912697 1250 627911447 627911489
    0xf0d050129090d021807030e0f0307020105030105040f0b0303160302100905190302010623240a0503040203280b010f0b0702120c0303161b0e1303030b030f070306050105030f07 77
    0x610405085c0c4100c15018001e000d43d00d64000b001046641c0121100d0b20161301505640780035081000340003030700401c0144000d0038544c0010092807100c0a0105441c602c010000c0d00f9900b1201420300c0894004408400f4154100504252a00380d03030300400903c00ca9496032900c0e2842205e000d000316103090b141f0790401d40300350321440040c814415201041d040045005144407a50406107102e0a414010540301c0031100b24064199000c81101030302d440782200055030a0340005205a03814010040b44226600341d107180c40300841d416404106101c801c0d03160541d64250181c0184103040c80e509820701c0420314420890700640d8045541b2046440f10f1104070b85400601180e154140c04045a881e204002298007030aa243c80760796100348400c00c85c80107649440c03140c460060108484004500c107044103c1c00031010034005e107408102952001e000c00d00e42900c00c12000180c1e844200300f0800d000140c401c10740034281c101c02500641c0710784821190f94100c1030040c071412880c805141400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 627913947 1250 627912697 627912709
    0x3050403020f100e060f150d08070f03080402181005040b03070f1707061e3e07060305040b0a020c07030b09030d05060d1203110f0d050129090d02 64
    0xe040012007210007646502038100f001d40100803806005201d6440170401124007100d4092250051100c50310590304200100102042c1d0781e402519640810020341c40420b0300241c40c081024003e40b13613503505043c03510500100b40c4522885c1c41c4500d5410081c0000720a04410210450f8800c07075011803524045000a818145654003604003110035060000702c0d1406200d03035203440f802c90300030754100560314a402e8580900c190343c14086008215890820030780200c50056000100c1041801c04c0d0034580c02c000503540b550300261151104503011259a08030400191000e080c29180070f02c00c0d424950f803119414000030f020b8018050300414003094040d010040840155001903030025181131100c8425200d5109142400f1120f05060000701d40341400e2030a007600c20381c400c00c403d440c038220302030450081c0100b22000707100d40c100700102c602ca41c0410001d000c1401c1144030024036541741c0344100b0b180c001d02c0b100c4130002054001d9080d140117903d005a50303460000340e900a00c401c0852002902c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 627915197 1250 627913947 627913963
    0xf0215040b030a09020f01020a17030a290f061213110306010909020405340302370c021e04060b07031722110f030106120615050a05010305040302 64
    0x6881c24040100440a5110b80148030326038002d0700c030003140718003032401242c030381c0d0280e9000340c09000032901d5101c44101020007540d00020b4035000107042991081001c0102092680c043c11300440143c40c081a80ba100b0640400000100e03101880c01140c208030305292580141035100801c004401132040c001ca0b0343c2e40b4000020024190307006580c480c0d0601000300b4000c2420b034012860030000038400c07187c05040c2018880b40411880d485405030400c00c040050500c442e9007050380070300990b07440c1c40302002c0d2280a400402a20301c0c0d030a08215900c4550031100c40c002d420008000700c02005603e550000512200b0003000c1880315000d0f0001180280c51181d00860141c0000101c4005150b40401c901c044c945484c0081901900c40b9400d260f0380340c1c140031240c00c48603041d04800000401e0a020070900c45409416003840260f4400060300311220b03507020044050381541604108149840740742507200c21850f00545060405001c1030481f821030040c0d03414140d803071011078241030080110300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 627916447 1250 627915197 627915209
    0x21e01060314030d06080703080906130e07020f060f010f030813050d0303060518010e0c0c0c091305070806091b030307060504061a150a0c080f0d060e0a090f021504 72
    0x1d02c00d400c0700321820341e41d601030a1199080c034500700d400305400700c011400c203088a40000d0085d0500420f107007000800e501c07010000c00000070718400000c600c01260000c6102d040244c000c1e155070703442002020309004008295100e0b10548500620600031100980425240c04c140f605480301070360911a04411002c0e000a036010301c5400141041603070640000c0b060310f400740d800d440402c90001c90001034410a00644140e0016140060a110031150181c500200303418111114505c21001154000f038080e101130b040040c00402c94010b1000400c011001482024001c28491801000c5c05860744407003891600c030301001308640d410342e0390304105513549140c21003c104003a003402d1601c00001c101440d0349211a5694915810740e41c80c05600b01c407210002d4a2106107060000303401100c1c152441c100c01c50700e00c0c070207119540c006a4104007030308030600c07020b100086850500400e1800003d0040c420410039040c0180d0100080036000703000a07241c3c2c1a10424980078207909124054011a0048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 627917697 1250 627916447 627916463
    0x4051608030403060f0c0819021e0904060e0708040303090809030d0c1b0501090b07020607150902040510081f02041211090a140f0a0902040204090b0901060302030106021e010603 78
    0x22800c00d0010005004880c403641c420424028109499410360324100c2d522408205018000340e0754190703001c2d00d000700c00d0088038014588241d05006503014502060062541200420800a43d04040c452500a040810041501ea140c100c0c002005000300a000608064a0382508004c021214080d90800d4000606542c1ea1220b100070080c07205a405200307540e440d5100c07000710f0b410300340280d0040c151903041c1e58040140c2c3c00e000c547c240b150700c08001241c004600304000008280850f0038699603100c40d40000c5506200e90042100391800a081100a200c0b440010000d500000503121800003d0511034414128090503000c000c0c0941d0b0f0000201e41c00405e00c90041180140b24a1544c0c40c0860b0394507440d40310080b82c6030403a0980401441d40001c100042104114000319103540a41001c0000c81e00c40caa40d40810107a030040d43c82041c00302d031100c41c000824903108548602400203032804505541c03500c900203565036040500c902011070a030281c400c0401003908068080d640007009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 627918947 1250 627917697 627917699
    0x105150f0723061f17070b03070c0506060303030114010f090315060e0f070c0f050c060d051503060405060703090f0203011416020d020304060806040f0e060601170103020a0e040516 79
    0x2e00407507802e40380c44240c0c58051503000a110400c8907813000022000c420001c0c01541c101018503003030110718800d04000d40320b4000300081c0410940001d62141b0516980d0b040201200c0c60150300e480380190006210390028401440b481390b000c4000200c4030001d02c1e090010000240d41600c4503400d1f9000607111002035420000d0499040c1c01c03100c11120440c0d8185016501e010691003003902c241c8141e00041c030582810307070200e002298144d0f41c50f03005205030303030340f01000b20300050031540311061941758951203004010418046054110180e0001e602406041c9000e0340c4603622131034005c0115052541e104100b00c140400c000c644051603501500070002c0c0304044011024400d003c039903100b8440945070401981e1440850f8144124525800440c2442d04200d02a102200000d2501e80c01542e0780c84400c12800310360141b005501f03040c01c06441c043c10100c0004048203d0780d01e100301d00380781c84001000142c03030381001361080321001d041d9200c0585482c0380442c00c0450507040e0742040b8141c0c1c98 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 627920197 1250 627918947 627918983
    0x703060209100c0206160302070b03040c0510080f1f08061e0c0408210f121005061e0a020a02030a03020706020d090305060f0603030d0f06030b0a050105150f07 70
    0x8010502203000300d40b0100c00d8040c0e50070031504540c40b020020b40100d400c1c4100da441041c0b486800140074442c0c0155020981c40782743c82040c0d03400456041e101c250400d8410440c6050580c225441c090003841c00c50748520300340003005005d040c0680b458440c00507030310039118040c03940c01d01c090242c0b1800381030300c64034208142c815040490100c800d0850401d0780021621084040044404503004403010b400c8010302c6136801c041c4907003100c1244041460803c451801b801400c001090030b603480502c041501c2c1401e0110200c0320101c1d030000b0b8090541041004c4490f01d449408480c0342e0071482a646d550600c142c4124181854030030000c1d0144102140b090803d500450070348159200c5608071056030181003401c0ba103202541c880034080780c0181c008910240b400c802070551004015085908e0000d5490700c4404031107481040f4a0f0700d90b038400d4103108114803e02898ac101000c0030090107103504000c00101c901d500807034858212480020038151910307220003a52926504034107401d0a0300002c070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 627921447 1250 627920197 627920201
    0xa0f0c080a150b010e0d03030504031e180806070c0807050a0602040e040302100c0c021e10120f0905070b07060b190306050901060821040b0d15090e06130212070306 72
    0x2d81c9468840c1c101003500500b940300d03c0400f000c1180051a0107903500b0251000c1d1f000b1f01d0054015400c0210904901c1c0b00090703e1030414240b08a00d40c5c1d601c8520882042d0b03003a2031505a00000300c3e07038000d0000d1007241540045000d6605800c4400559501924a0302d10304d0305c042c2d204000c2400d400460001140306400029500c5540a5000d441c0c8614210f0801000c4400c1607041d040403800d0071141c00c3c05800c04548c040b50400c0e800e42c2c0c1c130280b12840710000f2040d04603c8a500002640c002c600c00d0501080d0185902c0480c0d52141070010001541d26503880701c02d03902481403000c40104d03125060103e507070811240c0300741c041e001c0b41c0b1001111200840e211075a01098647c2da0500c40440e00b07894051103803400721040200500001c00800100810241040d11009220380c4d0501011900b400380d8001084030b00340c8454001400b45203880710280d410502d51281c80c45920b4804072140d500300c0443c081c0d80c031072050141d010391540b4920004100d0410510206001c1c42018404020006c541d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 627922697 1250 627921447 627921473
    0x1c090f08010b090a0207031d040906050a0606030c08010f03111c0c030b0711060403050a1206090b03070506390609070924050d060207290c0a020a0f0c080a 68
    0x1e4a80f000a40d40703180f07211080e8031800038010000b903503d0080b000b003000014071481004000034070214002406490740410744c0c1040c2c9084c800950703620800c1104941510403401d4400107424020455850140820404415480701620b0102c41c0044100d05951b030b8240d512a0100054441c0d040e6a003904207180c00101c2c9000884990050030085100b40f8020128042e4400e4200d0042040b5034980c2d404683e542c001d40f1a1320144600ea0b02000e03c035030214060304014140ca1140015191400c0042518204850f0b0000303004e49020444071100800c1c2210b05011150a98034080703002c02e10214a8850300c0e01201042518003428040c403600300710120b402c0c421100070380010300400c2a48e9954443d410900d007040081e4905420341003040d8244107004151803801844010309001d03039515100e104141c0660002120380c070859155051203065060315410544c007014050800300698806551f600086002030b004580c021590420800808030581c041c0106000380c1d10448180d107402d400f80d03028 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 627923947 1250 627922697 627922699
    0xd020c1603020607020f0a12050c0a051206070806010e0411130911090d0f2112060f0e0a091202160e2e0b120a05181c090f08010b 57
    0x40c04808001140c181859a000d8030380007058075241c46000d07401c00103070900d01582d0790780140050000280044c602c0d250344007054007a10203000c007805160100980e460b2150000381c8101ca90181c450320388080011f0841e805000e50602c0e0f0041d80b6560010703140c1c090030380025540941001c1e1000c00c2c002182d0701420910103040088040c1c580c50b50501c109480400300c90981c062410702422601303250030743c07100d03038024002c11914000c2e04c202d4850020409505840c181d58014500180b60481c0d8042480c0c0012100103100700b002d5810407408401e01400b5100b4001c103070002c54049a1038080640c010202245e00c6503010ba0f24000185000c2c6d01e49042480030844851404800941d0352048040340784a4a00e400420308161100c102c0300c00002044a030104074130b40820804180c2c0042400201421020942211040c1c5040c0d0035a00944000400346c0000310041010316015800000780442603012a1580320031a84031140202c64007e0703507600070640c241c40c0420001c2c00e94010344c0221680d4034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 627925197 1250 627923947 627923953
    0xd0303060e15060f0a0e0d03050c2a1002030c010603030206090f060c0301060c03200604020a21080a121103040b07020d1d0609131a010309080304120c05030d020c 71
    0x629400b500040ca4200040d80e41c10443c20003400000e840ca000007096050308900f00304203031110200100c0d0f81000010300c100e01045c0d000441d030500b883d082001080c00151010003140300100700c501030440121110701507000e0300c41003030300000036402803065508242030780c07000300025990780c180255103060980b0403000c070780078400c50204440400300f0715a00c03e0300e400205c646964a4484126240c80c10381d48140d0821204403603010301c0000052403401d90030305200080442d42464010041515910b50013046005c00340b0f001c10600b409100c042c4880355070000305450701d03044600400d8400d00300101100388030740e142c0074411144c0e49141c000f07980282d02800c0791814682da0303c28141d9403100d105002d040840d40e002c540404541072504000f0f003954010b000a0b00b44210140807400c2c109a54003440101d80c1c8a5034420702d02c071110b206006108109103014001d50304607880b624618400031300083c014035070340b45a2140d030307a002c2c24801142c0c40c0d202040765034a000c1c82100750001d4210b8594540140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 627926447 1250 627925197 627925201
    0x130804081b0a0b0f160218010e1b032a120106030c1e0333180203060109140a09020c0d031a0d03030f090b041a0f01050108010e090c0a1502010f180b090a020d0303060e 73
    0x42e048114042b03c3c0f0180a0346240b4644410101c41c0b20000700c4541e060324022042941d1000b0b6509101405100601d102512040d5040c020042c0503240300960000400000c400f4281c00700c0021103c84100d600d40d402e00148412140402054150310500340500001d800c5496a58410f40e0032601001c80e03210f20301c019440b410f0784040b0402d91000360340250008042540510020402d0018007480c54002403200000954034a0b280d41642c0109640210f190410380f1035840ca103405000780380303a0090049166294030701340340001c0c6210700a22009000c0541d55400901d006507a984000764407500240c648205c0d00d0035181c02c01810004900b61070a18840e070001c20300004040e504107069480507100c6111076801c1c0007050303a41d4600240010301c035116908000055441c2c24042c5000307800300f81c0000c0380d42d03090418064290303444c07024403418041c60b0107044400c40c1c100c2c0307065481a40d8032140b400e6854030751444e401d05d02400000080e6019401241071010550107a04c024116140c207036000700c0036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 627927697 1250 627926447 627926461
    0x110d050c04030507031202030c07030308040209064501031118130605071e020304050a08060f042a0909060b010507050a0b130804081b0a0b0f160218010e 67
    0x24090751100800c3c0e684501c00c03d100040310564408001c0c0802c0c8101d9060504c012003407403034240329034020780104684130280015800c2a184079075210800350f404070b003400c1c520340f603003210740301c80b20980900f8006124000d820440c00a840010784000c160459840f03503140d0134401d0380e01803100d41080c8608540074075070581c01cbc0d40e42c0c2d8080c411824654007120f4195643c8804001d0703c0300811960070030582d41e00b8228901540c140d500c003c00800e0b8019070304c0d00e00317020034054010016049806590702500c204050398401400707140d40240d00c00703180445840d42d92000401d00526034007800c8452041d00b800300716401e559001e0b013201c5004005c18040c070810b62005407a9840b412030007510b241c0094114201289030304036500e40000c0c0908012a00400544038449580c0141d0800a1150402198004042940055850001c8041310756130612880d2002441c2144135400c012400c040001c030760101034159000b803040c4d6080d005008142c5207c480040e101061000340542c0c840385103000082410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 627928947 1250 627927697 627927721
    0x601020705150403030f050906070b07021b0d151d032502100309050c031e06062e091a07151a060f0c0111040608070806060304030e0a0306110d05 64
    0x15a00390328181e183c1030030354508541c100c403510916024080c003048038902c59224100102411802020f00790014145114020304201d00c0541c500003490841401e080c45542d0700c4116264580e00010a50140e0701103421800038100e9041807a00802000d12143c0c0004000700003043c42c4000902074040601c5a20302c080710320510745401941014034213201d40381050107a400042207034010f004490b50485030340e00003481d2001c0340400c41480084460800c0510f60204100350b00882d04075200d90000000640c0360340e02e50200e6110460804160314074500d2140900706100140c603140141c010300f010341d201d80081035401003004940b052049808080180e0051150101a000c40c207000140c15804a0800a241e00800c51903181305a041108023a40102441003008010482505944842ca0300901030211003006250806000358802080020b540da0022294000e81c142400c03001740d035804010078034403085500001c1465290590703003028918404007514039022030303803400d014030b50301d00d0303140e103a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 627930197 1250 627928947 627928969
    0x32d0a0207060e180f09070801050106050904110309060606030712090b2d010605070303111615090302030313061e0213080115030605061909060e01090509060411150c060601020705 79
    0xa12492004140185d40c5540f0315608109404100c810f229151482c81d42120f00a070302a0f001324000107104000d03818107005503055800c900030380c5030445c9000c100040e1200e10081103c0e12880d800000209000c1c00b80304028010130108004000c0c905640ca4040400b000c192008a01196039480201c149610910314084070603501150016607440d0440c1a40c154000c2c442c100e0038507860356a90710640d858040502602c3e005413542d5000a45d0f5828681d01541c989a0508040e17801c0003040b80100390004100da8000e00500e407504505a00c60030100300400034072010348103228a0040c14a46080d540d0068220400c16254200101d03907140302e018220761214007058000a211301040000c00d20540c130480d405a0b01921145241c00301c100903068103010f94010a0781d507580e403d0f041c4460300c2e040c20214094966000100001d050a828142d91290010002002c4940340c901c03440542d100c032503c410a0045044609444200181d01c2a40b13f0408840c11401403103104400940d614005d078502d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 627931447 1250 627930197 627930229
    0x7020a020114070b2a0c0606061c0c0804020f030106120605091c02030403050c0a03081e0d0f05090f070302010c030e0f10020d0f050903032d0a0207060e 67
    0x440841160340c015540003403034051141021405211100102e280c100105204880c0e41c809402c50f682c1c1070040c015020010f08140c07050f60810711440c0300903000000c0c0d0f10340101e0220f0b107258884429801c803000c0040c009030701301400360914180220340390300444003030f0040344210f5204464000031414103080364402c1c42154500d010307800040340890201d5100b40c1c5c0104185094660041d07922003031111024004c242e401c010780c40050104103121041c0480c0c0307a209411214003003910710710703140e0b0307103607070107440311404c454850b01c41c440c4201000030003100e4a1030360900e400d20460041501200003003070b0854002c178203401a110012800d20002c200801a03d40c161a0018543c140d52811911540120b0100e40c205d030703042c80c001c0788503030b40c0e0b0b82c1d04804408240e000307200340040000e0041011030074030b10320003c0c080d00313222000d140c0d500801902c04a0340c14820109504440cc480b40e42039110580340c10121510000301c0711422503011404105441e8281c5074a00d030703009020180000307215a02025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 627932697 1250 627931447 627931453
    0x706050f0c0f09040b1f0809060f07030f060306050109020702040b101b0507050d122c040902040209150301170a0c050405060f03011a03011808071218090c080604050702 74
    0x1051150300d042c2c018200089020300001644402c000200d10280d8840c20f090030b10545000d106d0140c01c0d8007038501035001501c0342c060840c50401c54828101114041c0100c01815190490100d0380703081c550042c4019900300f4170500065a550912030001d51100c00140d0055082c5504050182484046980b103211103603189010303e0000640101c032800020411a02d6005a140004169544c031785030817403007030156850440c01410458050032142d2843d0a0406a1022070080b0250308081201007140c100140d40220f8026080d05c0014028850900c0342c65204500b043d0130403c042d00840603505a90100c03c0545180c5183e10300990360340c0e4280001000902c25000500c0705050540107150805005400e41008180d5200003c0c2075401002c0c40309090501c418241d500352030240a402e1201c050780f07118602c0c656003a20b500080e0f200e20034016180140542990062034840c146500c0c000344140c008042213529040540c0c007519490000c04005146000411114a07061240c1405518030b0b03001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 627933947 1250 627932697 627932707
    0x606151808030d151206050a0c0f020c040e120424050708031302130f150605120c1e0a030c120b03031b030c2d160611011d01020706050f0c 61
    0x50001500d0740c4100c3c0307000e01c2072440e000913150400c00c042482c0d9034030031b403400705191512807500c4080310346440c030080400025422002e5000d0f00400c00c1042c50500703480210381d415040e06202d2419113440d00740141c1c20750000d00000c003c0b13114802030030350703540e52154821507603001841114203018030940038040721402c00125150070313030200c69103008501c0540040c000d54080ca09080886034a680c001c103410f41c070b803920760310700350152005040589440d09016003000c0400e1000b4440c090001c003001e104500005801004070482c81082010360480401030380d4a580144004001e8400500c4000210740c203203d648212507241e02500c010b44202400030342c03c01e10f0303c0b0740424000c02158200001800108050300200d001488203080440c0c04141c8000d070307140a41c510b501340601e03141e4100035030b821250451940442d0245114211802c61502010250842e04500c2c010a07050104488801802e0141a1ba442040d0060000745019210402241d600c41d40349081d02c5004980e0811042c8040103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 627935197 1250 627933947 627933967
    0x2040b030a0b240711120a03050705070b0a020f06060a1a03270f070e0405070303082203170a060b04061803020d0308090609031602120a060615180803 66
    0x40860b0116030000c04401c0202120120a07030740550001c10300314400b00016030041440341040000f05d60790390549880388000c2140040fa03440b001c0ca600c004082080000d1581c1c00e00130208095005842040c0741c2c140d0300c40c1d04e190080d543c1c003641401d4030351074041e40c000a040d0307281002b041002c41b8041c410348180b054208200e44140e0340000c00d0700341d13201c0506542d000c80b60b405101003040c0d148080d006200817440b01e41c07064034052941d80600714140055080000049010906404a0781e0604001c121a103402d00c10000030380c050426030511442d803856020900d170b8814000066005005030320a05a10b80e1030045043c0c480f58014582045002c003c10403a06110b00450031488150100c5015415101d41c001034144a5040d0281d0019070188240581203a041c04241e030403900d20402185400c030ba90324680d064002001020388076400008295001400901c101c2100c564801410860715441d0b465030620308188510084c00101401c0c09280c40c02c0c0b10072004420380c0e0b041d034015800d04071100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 627936447 1250 627935197 627935201
    0x6071d150c060912310306060f08070b1801020a0f050d1b030c1104020903011103010e130c0902091f0215090304030b060d110a030c0504050f0402010507140c0a060903060c0302040b030a 81
    0x204640c09108405ca078403a801074a01c000c014091440f07600c1c049009460080380c007a41280c16041b50000c2c3c2c10151080008110304411078405000c02c40c5208099400b03500180e0400000b180050070301d2803401c110500f045800719030401000c07000d40705c0310170403014030300070220b40e0b40c5001c5c001340440d81902c000400305840d0b4118808140c40200098908084400420300791140030f02032010040c004001071141c0580d03000e855600042c0c00758107518000c00e946901d10075200134032a8050300c0e50b0000f4803004035240e40d03c0c240307031208410009030348551030b00c0d4009503100d81c0c004104408140c2d010100c0d11182c00801102c003202c0c0c000865071401e80b98902002a1820543c400316156801014240ca4540b901d500c00c2000314087c600d210403072841c007130a110940b0b200900292003a00d0000810006070f810500f510714081d00005180305c3d03030f40c00700149450100307840485544006000c40c009541c5500080c20000e403445480203000020500f8015010780c095070003028001d04090002440c100310179 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 627937697 1250 627936447 627936487
    0x408120a1b020604050f01090305070602030601140c0309030106090b101b05010507110708010b1f0e040f0209120304120f15020f0714060906071d150c060912 69
    0x240c4000039189001203840c100e41c10408400d0005a0030900400084c01010701c9179000f442000402484146000c1c2d50003050342c4110003009003a241d0100c00302c1d000703903c1016080040c0807110305951b510294400413581e0307030700701c010031900c00d41c2072803c08101002d550144044155010742406810840400c068601c0713024012004000c07403c1c203100034080341090203914080c43c20380d1156254803075640001410410b82d034100f421180e0510500080319128450700300f400044007140010220340700c2900f1200c8032002d2014a9009050010710700880c06c03a0f90040441d20412140c403540e4507590240c0540740c0c000c510483d00e0740c456020341c030004114081150400c1038850f2408000c0c04511011020898001d01001c444120340494403804005264000d40001b40d0703854010002850002407c580c1ea0800518610405c500a1540d0080e5003800b054011054802040d4500c808401b08000441c0c0c1c000c407a000c2894410380012408000c1c0201d00b00d031500700328000c0e40b4a0402c1f4000e803011141c07a8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 627938947 1250 627937697 627937711
    0x9150614120c1309020901080a080304170c0a050106140a0b0d020309160f061b0c09020f040315050708011203020c0103150302040518010c09080615120303041a0f040812 74
    0x160b940c501d156070380d421400b0f0304511840a0001491406130050101680301600242640c1d40046a40c80200750741e501030300c2c1d02c00d034004002083c01c4408007107980b031401403580d214010301c1044206010440c1c1908010103464078026043c203100400003c0006030300291103504c000c02c2d000c016041100c075068000303550183d4004226185042c080d00300d0f01d1065402d030f10035005184103a009100d5a680030400040324070380002c90260740641620380701d14039543c03441402301d02940081d962980516010039500256003100301001c044014030818401781404071440340c0090001d40002c100030000c1c4515040b030b030350994020409010780b10700550081c10500421002c4801406000005940710302400384100c1100c0502070b0045d04a201003400d690078400a041485a220340a00500c0070025250398000e8444034260070f0b0a0215011668500c43c0303240ca0340c028040001000180700e5042c0c00005013103542d8841e0020765480d464074140704c0505640003009444104014124120360005064000b24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 627940197 1250 627938947 627938953
    0x360f04050a06030213050a0f110a08100504230603031c0207021c0f051c02212101060f050702010c060917030112060506030c150d0209090a0915061412 66
    0x43c40303800080203642d400f51244078a0782c0f140d0400100080600510808880000c000c0c08540010b902d01e40042c05075540190801041000264400c050150302800500c0080c00c03c2015461b6004e280c0ca11080c14003070850660040000300f00c1c20b050000c11541d40b0440340150040f29440d1032402c130040c0d40107030002d03a444401910300341000030201c03010300407042c450340d80c2c013004941340d1510a0500e0307441440c17200844954050480b041d41c0100c2d02181010342e5490512220140a001d14a5402040050058103d201a50207400e662001503903040c0d46464440399140841c00b40e045500380b11750807000380062a0105c04400107220f6802c000f001b91702c40c450040000f010760703803400b8194100b43d00140807210000032000600800384038554204109401525201c220b410108030083d407001204444988001940311002e8843c2d410f0f102640741c01050940182000120100070b0b11000c0c1042d03a00d5026858010260010341c071a000c11500400d007a90540300c80c0c44204042c906002c0340d2118680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 627941447 1250 627940197 627940199
    0x309050709140703090209130201141b1009080d020a050d0e030a030b03060603030406110304080d050d0e010b010e0f06070204051015020303010e041104060b360f04050a06 75
    0x4009000440107404103010008039074034800d2500480c81c80107812202494581008000541c03503081c0007607030219000b241c1d48004011480103c40b000c82c0e00a003a8455003003c03070103140b14129512401040b60b001e2040b20107018284040100f10341c8043d038010400e0a04100e80301021960790050540030180b41050f9040c2019201440e003a038281da40c1d240b8181d000052510300c02c507058403c01001d20343c154000c054621f0000c005c26580e100703a00940c0b0074011241d400801c0300c20104100c07000b4000c0442a10b04003a21083e01801c0d03504074844401ea82c0e030510241a894860512580c0c8454405a46818803040300b201481140341d26000a00d030448070401a420158a49004850152510b151400d80e06490b02205085000d0040094030440d00b007000100032562107040c1d82074209401c25800c1c04203890a100040c014011584900040c00c40410b4042015441400000c0c030660184001c500b0203c81c210501c88606e81003403015800340b40221030410781c0c10542e010a6101c099890005016 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 627942697 1250 627941447 627941453
    0xf06160c17070c05041505010c150605030a03030506090705071a070207080708210a170c16030519090825081c020706090b0306040e010f05070203070b011d0c03070309 73
    0x968040c00c1c0c10f4079003010041042241342058410703211800903002401003107a007040002080b202141034040c00c55800e1682882e00c242c00303a80000300400c4001e0848640714040d00d4044e01601044034494440c15038a4001609075000c1c07030855444583c00701660316080c1c005030301c0300301e586005418a421440b80c3c0f08041610386003000450003500080004103485034803641c0819158204000f035641120090242c40059a0000d06407541c0802580d0548103030382e1880000740d4940074050a00c1250306c0c180750180207254210006003038211b0046418020500c01d51030954a0b510355220301c003415800b8031454400c845480300f40c40c0702c082d040c240e46075071190f03500c801e5441c0012000c0c441040c080020300510100d134042040c4c0c4010712142c1403240e000784c45e100c047c105a000084c0310502175512400a00d0409c2c01c294802142091001000c0006040050340259242c01011040300d0182e140000407500c06040e815200b013503c03440e00040c0b8956201034414029401c040c0c03011040c59201d107035903000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 627943947 1250 627942697 627942743
    0x2e05160f0e060a021b060421051015030308060a0f050f03030d05010b0a0906110604170918010815060904020103090f05101505041a0114040902030a020306030f06160c 73
    0x18020a9402040794108800b00300405114880345c0c240f081804000800c8400381d41d42045c0700c4407841100d0684041000c0c248181800c00034040c6941c00c0745400c1c4c10101d5060004601401d50340aa0b0b1071040c1039440d041801071205203030141200f1121148000c00c0f01d803801941064a40c800503041c1ca04102c8404888029500e0030381107811400c00200c0c205203103079800200d1000401c0249880c8070008044031805071161781c090000707040742d03403080324030445004290116425514003800d000d40e00280c04030000c51001081c09031001c80e006107004030f4031400001a40d01c1c041c140090400301c094840e540103400620144200722503440100c908040815411b0040c894204040740001c030388492103000590800c5601d07005a841213190240e102c5002c860b801e1603119002080c01c142c01a42d0744621241860702656000c628000d00010402404440d940c02a5014100c00e07402c56002088145000ba10f400c402c448400c0040081d60101c06641c2c45000703060318450182c00c8840500c400b5042d4840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 627945197 1250 627943947 627943957
    0xa06051317071209152d031e09080f130e07051216020303040b0c251209210602090d08070b090c01021b040204082e05160f0e06 56
    0x8800302010900509010748480f14070070028151424502c1c3c2c40c02c0c0755142107440081030550040085204c21006c403800c2008422012201c1c0480d8000c4212920b00d0050141071400014504003014440d4034044208600500e03c0c000d512440050401c0c082d0003459000da000768182c61108110f504002900500c0031010354000c80e07a0f6070b201a518840030480c04982e88000d4407500c41d1040400d101d480c41c030303800300c00c0da60480d910020801c0d20f521440b54071070982c040d91040d0090b240c28140c4007096241081c0300c1000b964403c10712120200711228081e0344440807840303005100c1045030510040c8020480ca21404503100d10401403d00d810b44010480d541c2c040201100c4e00d01c1c001901005021258512991100e0f07190000c05010203a400002d46400c83d00084000700c05003a0300400c1c0f075981d00c1c2c050710050702c00101103e56114254078031803894480321582203800b86015000803011441401030740e12441c800e8203a000400c1406030201c4040841c4c100500810040d07141040043c0d8440c40100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 627946447 1250 627945197 627945233
    0xb132915030720031c050405100c0f1106010b0f07031206170c0a06050d0c0908060c0301150302130e060612040c0504060617061504080a06021315020a060513 69
    0x1074000d811042041d031881040400c0d000d0690700c144100c150700300461705801501c442c103550200780341c0c55030700d026031070210844000000c05007465075080c2480d83c0901c0300349000219940b4485400300d40c0c5441925141d00b801190078100b8100410100810401c0c020883c0c1c0e4840c2c0b403c0e400000f58207072000c04483d880e81003e00c12020003e803581081000308403024180c802140c180c500b4500d400c0c4064802c2c4655030341000c40e15240c40d21061030070700541140d0014600101170714014035180307900744c285600034020343d258811400d5010404911034070a6543c0b02c0c14540c100c10020381494090103160300d00a10495001000700b14204100090b440c9080c0524030413411402c141e07041c20300300710546010f60840c00412100c41c041d080b06c4c8000c2071010342c0207001910030b0a04580c1403da00080b40c8240d400030703d118401c400d201010888160f00514691a2020a5218498982403e4940001d8440000d40142e00484812000c6036a51f840641c02a90808030415024441d540b1030b50404104510b42d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 627947697 1250 627946447 627946457
    0x203010909020a0b0309060a0b130e0303040303061a07060515120129060d02030a093009050d03080709150e04060902121311040501090b1329150307 65
    0x1000850a03c03803019006885900d41160031071910700220366464030b0041401208685030526910551159a10020300c25150242402000e4001a00c141c0e07035842540c048002a1038107000040b910038030a560b400d02090003821500c0c14085032542c0300a0f00c0082c1a000c042d07801d548031a03601e40e444880c01c200b9030300000004146240c00f0f03070700103045d070b000714540c2c400c05a030240e2194015035440f0704903245d000350344100607101d44804042000400c100340703008068449943e61130006600c0316186140d003030200302484461900b010b40403540390005210b82600b0202038200d10001034010002075030b002c40701d441c00700103032aa11848141c3c0d100d10450034002103040d45039081c04500341801458090310300da41d400d5141c002080c9200304440c0c801400d04400302c6052000800700000e16400c0414400001c00900c1350313503101e8010f02c008049a0550a100b0303c00092181d844100c5401348234401c0c030b0b6401c4c198601c540108010130f602c00020798501c0e48151801e50703982500062802450064a1a50319 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 627948947 1250 627947697 627947711
    0x40b01272606090613061515120b3a050304090606030f050610050706060b0f0a110c09060f0a0909030e030f03131505400509040f0807050102030109 65
    0x61142800c0300940f0401080d0426010030407001441703110545840d61200000640c1c1107694080201e07034a154111200400b103500e051010700387d000c15042030500009800300504800e140800030784c0d00c00c02d125501c160b07c241954040d00c1d101c86404401041c10b41e480201d001241c0c0d611a42543d00940081c11300d20303900c440030300c401681841030901504a034001045a81441c4d800981d5040f40000c07984100b00d00010b000c8100081c2c0d4000e10000e1031a201101c1d2619050141071000b03400c02c2c0304510000744481c011900032400010b24810034440030740001c03100c3c0c035000141302030900314400c0d0030b811039880a000104014148211070f480b90003941c4012100c6502e03810541003060701800041150701c02c0c030412980c2441c2d05691b2040b80c0310300c80303140c024440540b02a20709000d01c3c40c011148a9000307180407110010380ba4080c14900c030300e0058034200c0070b000040030010b81c814020f40790010361800014000a0701c9040081002d40140c85540c00e12195640d041d0a9920036003100c1001d54807010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 627950197 1250 627948947 627949019
    0x2a05040b122506021605090408040b0f0d0b09190b01031e050403080606040b03010b090a0305031b0111041a0304050313062a030206060103050a0f0207080315040b0127 73
    0x4100301500251000c1e01445c6240c044880703c0160714000c5902c40d00320200840c0800c0072043c01c850042c000640002c0c0c0b10b0101c0003c2400036040701c000340b003900307050080c0304000e4070f000c40368503201d0303c084040207640403404c1007480010820701c124141496999a121180183e4000069101030510000450280391900c0d000b0600840500007500a000a02c01403000201a0303084d641954030704058070703403500300e002c0020741e030074000781c0c409442da020007c0d4001c0c61015811514003544040e43c000c0c4500d22078110107030b041d8440c0c1e20540c0109000a19824443c0420710021038010340901d0840303092041007000501650340c1940003401054407581303d444d08121056020122208281100050b0f070a251800703500d07801c00601036810107a0b100e000541c428500d501c88581c090007154219140d91940c07900c15110303402510664088607000e800341c4c2103890320b03000c2c45c415040180c0d540b0760401006407814120f8801403050f0407550450440c0803075003070304910340b42c803d0700146d09000341003071604a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 627951447 1250 627950197 627950263
    0x1c0c050f1c0b030c060a031a0901031a09061b0f210907060c08030a0507021e0312010b130302060714102a21020408060901092a05040b12 60
    0x609140203130001680814141d0b01d55040da01601564100820191001e03040c88a924200c5d40d016a44a03004030008030a02107450300805a01030b000f440700384503444500345140c2c0d40b0f1040b10139594054032042007406500caa100a80340d090903030032000b03003000080202000d844449000b16862a0070b80c1040140750841001b00303800522003410002c0c0d0703803401070b2240c011900c00101080b01c83c41e118000308004620812000500c01c0c04041805120703000c00741500d071207501c00e030000303103c070b99160001164641040f0121014a10004c0031120050700c0c56003400202d80000c58180c03282625542c1d0030030031142c01e04c03550206d800d070100009010f50f501c840307a0403000001206103400e00c540c0d402c008078613a080714100d1881080e0026540014086101d140c4c0644140d4010359520b0144400340200c4031015006052058420014100d540003000707418002c0340414a1140d8078142101000c00481c2400c1d4812510303003002030454602c070f102944045103024041a2030000740a001c0410426801ca04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 627952697 1250 627951447 627951461
    0x30f1503032a172a01060f1d0f09030f070c0306111801030b19031208130c0b030709030b13021905030303060616051c090b1c0c050f1c 59
    0x80e0b0301030040156124040d48240d00d07031001070103010004440c00c03c003409440b13100c51290200d083d01846000c0c9110303079020f003003240f06014240480d00008907203001d03d030140c16007007421030081d13080c9990b0301c00541100d00e00107000d84039640410015a46558100e00090500e24080d40d4007908031803071031410070201c40841846860601c002d01c08902c01101040302005240c00034600131401001040004000c5040e000741d0300c503005c5108100004000e80750300b5403244030126440e45c00c200d640d111001034a020300d09070020b040039a4400180480380c100d00285030805828681b0030075058403981c840700b0540050b00c15299819190848404618207043ea0444100000d81c070490010b1510f000300b07649000143c000b82c440d0710040355601d400215503505040d8590864100d616094070300c40a08100013406d808200051502113001c07500200000845541c00404000d444403000c1038620900244103805414041250401800a005280a01074410140442d808001076018001030504580300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 627953947 1250 627952697 627952757
    0xf0420010c0b07121805010507080403020319050d1d0105010503030c0c0f06070204060303050a02100603020d0f0303090501020a0e0f03010510170a0b191401080607030f150303 77
    0x6406029126903805008100480e500030064403003034407101010b54480410303400443d0094a48a2182c210408110320709052500410081207a82c544d08001c84210a0444e40600580d208020f4104010584040a40020094500a800e00d010100000c2c152245000c0503510710002c100c07520030030407007845260b0040508500030340c5006114a000360300c0d183d4101d2194807440c81c0740300540d103c0d00c039081195003140e402001042295141e140203011a040f01082100601c1010049040386a00e48145001d5940050008030401410f58400302a210011070072000c240e1030318018400180c0c240090003040f01c80e82c80b8a00f02c0c00141090140003040d11940c03d1103a810030b01805401070301c01d003400c000c1e9031601e0881c0c0304d0220f880110302c1c03800303031500700080406590341c00300000485c903402d85004245500b50140031429501b80c039000740c45000e0181901c02c0c1c0144000c00d00060003540807445a403400b000100b11075047e6943c24211100550040c2c0c01718484071440e4010904407601102d00440c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 627955197 1250 627953947 627953993
    0x30f02190b0a0e0a08040e070f08010e061005090d0506060f03060f010501050f07170409060801021305190305011a180c1e22030b1006050726030f04 65
    0x603050301ca60204000152200c944296500341c03205400c0c406014140c44103070020441c4c0c1e074541e6a01c4028022000c05c444690010303036494865007a013482607070301c02c0c1295009210b20417030b92100320801c0341812101803001c05100341000320040b10f88486c03c2d0401c0c02c0f40140c0252a481c07612100f44140c2440f5465803520036000300040000d0884000e00150540e2020b29045480e02d6540c90320400c030380728800000c0c050300080e0840d02450f0403154003c005440100c0c006200055541d08458243e018040700c0c514080700c200410701c807500340300d030b0000c80c1e03e821200c00204180d0b50341c8130356003111640c086801c4104000d5000307140c00d082118110b00104c074203840b44540bd142808090300380d03000300c115407044c01111043d100190210780040d80c400c1040703202400003e1103400003001502e1241e100403610106d4450001c2e1091120390300c0c04045800355281c1e40d103443c0082e52100984401c112480c8514040030b030071003000c24801c0700914882c1603001750304c4002e401d141c00c0440c41d0700c0c251814805200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 627956447 1250 627955197 627955243
    0x2517330603131b03052d0d0305103218070c050a0b071e03060f0306150305060c0a020609121902010b040c21110715060e04030f02 57
    0x5103841084a03404038802601641c00c001a1501d071031408003010758089038600e5504003005010000c200703034402d64100310140040c1401700205040030b0100c041ea0942075007007140e4202005000350400f42c1d05c2a0040c6030b8071080e0303803151424208802c2c1c8400c0d0f1200e4290414035840c410350f8440048521400c2242c04102860702002d4094030ba80c0001c1500701009154076607441085810000040d8140c1e10642d026181d1034821001400c00c02c059215051001041c0d500014031030081c810f440642d9a05840141c1d0789065899000c0501740101c40281c00101d0040004003080c1d0601099010ba12003c00c00d0307954000e440c50080c03400c1c0d4080c00c00d0380d142d00f020b054040c051400c1011030320b48009040d81e07038550303500e0904168018610382101a800a042800f211225a8880305054045580d40c08150801d40e00c04da800049031244c0301a5140840c00b0400000400c81008410240c1040780c0800305059854004114080c0d0341610100d001c1060702d4200b201e516011310446600064060445e046c1d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 627957697 1250 627956447 627956449
    0x403020405060a0b040b16050a030c0209182503060908030609090607020a021302090405011701151203110f03070c090608030a0804020103020903210408070e251733 72
    0x185c80f81d441115a00c01e400525220650180041c10300c0998100c1c05a900d01940da0401500c6032188500c203d00c40c60605c00001c802e04a140c20090b008582c0f1402004001d041d2102444649280c00d200403a0404a03080000041c4240c010007040c0b070f211b2200300b500c03401c2080c28407455480161182c6100d130480c2c800c2241459000801003003164040702d00300d001c40c1c2e180c941c140082c0b0585500079049420130001051030101100d00e15881d51105008006000f00600c42d009004c906028a001e00300c450407404010030711070f110150301910003e040e68624000e0400091850703100f08412560084801b008200c4c4075001d01c9118001c00455015500e0005440002482041c000b00000d052540c0410b05404d1501c0801808000c0c0083c00b007005540d1488150302c90141d001b900c030303a140c0c500c503011020070074100990382c01340a40b48505500c0c0c1007840608264034441c1070304100788204200c1000f208000b1030b59464040c06040d0340400b59540700300d010950228908200c090300d00019022280601e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 627958947 1250 627957697 627957719
    0xf130212250b0702061608070f020f0a031e0515010609080106120f20030a05100c0c05031902010b0a12030206060102030414150c03030702241605131a0403020405060a 73
    0x110f954110307207140e582c0c26003456042400710b42030005018550041851010850000000c0c00714500807186004104044010480650040d00005210b80301207078040b100100c8401801c082c0c40d00c0364068818518000d0359105114000741d10040000c2c8101e4020400c1d20020b20580c4068027050032159500d040c41d445007102404030400080011012035641d0303120720400d070401c590011005050b1402a41c0034209207980d41c10313516110014a2508110a0b8668001c0600c4410258820041c5080a051300081282000881801e05c2555200c0414202580c3da4021001c05450050951018101d26080080c13a0050040001e815940208800d00c0881c80c0001035403100042110f510794801d400c00350b21004c5c2d024001c070b442405c1c403020003030008480d008100c0141408100c000040c185650320180c14806000303482450b10890845001000c8612440060004580b0203030007105d031b69669102d40004a00014944560001c003203818011890540103581d00314100301d0f00b13213100c5402c1881940b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 627960197 1250 627958947 627958957
    0x1060b12070c060c0e0f0d0c0608131707030f1805060c070e07090e0f0105130c03090f03030609180c0608040519050d1101050f0f130212250b 62
    0xe180c0d0050400261003034464440200c0d02c0ba440103060190311000c07800601030030301007204188103001081a121141c1408240c20308501d8204d01102d0f070691801c081581e48050143c1581402404400e20401080302c000065140306031407040d850f030715407290070010b04001d09042c0400c10080f5011100d950314036840c91402c280d42c6c0c12510301d6500c480c124042c500d4030b440d5900000066801030108510650880300c0b0404a508a07182484665540889031100385400d0240d00e5020f00000303007540301000d250b489045452064100020300b215107407298110310340a40e00031000607072a0324080c44400c2290080c03106050b82060348075150140c50340e50010040e03480c0920810402c1000004045c4481041740301040c0f05600ca01520080841c10402e40b52581d200c4010042112003c000d00800414400c451246115006011098a44a808072a0f049000d0700c0c00100c1040140341001503a20650b414000001010081c40c0c503803030001545140041e08030321000c3c0c440b10305204100442c84032003216 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 627961447 1250 627960197 627960217
    0x206150f0d0212011e06080c01080708190603050a11030f010c090e07090f170106050603150d17120405010c0503070c03050a0c0804030b0708250309060e010e0601030c0801060b 77
    0x142e6442c0c82000ca540c01400030340c0c01786110300070803034050304007120540c40102520242c80941d140c007902d260064608000075500d0034001488400010007441c5410188002ca084c009070210b58250380b80c1790545031007000c1e0310940c0c1000d8100202d003950303c2c08002d0228019a0300e4001c0c80038580703c5101900720307011441141074100c07854000842641c412802c600c041c0c0700400c4201c00d0700b51198800601c0c010400c4000200f50702c0d01c200440e40d403402c8400c0d6441440b861205441c034281c03240c14404c002140c10800c60b500540d0341c1c800304501522002034125000c000c4000407451a003400c1c4903007554428022030382400810824800240d6101c1c2010705101d800d030402940c0c4000f42c440482d002d41c0c10707020103804204041404030801c4010a103490294409640744c01050b00c1e074034401840740d81c14415680402264920b6501d45034044d402c4965000e000d03200009458000c0001c1d40c2c250b500c209010405500400010710403c215015284003a000ca00d00800005051424840c0ca5101d440c0c841 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 627962697 1250 627961447 627961459
    0x30720030f07060f060303050d0f1815090b071d0a03030e060a11190308060f010f03090f15090c08010c02030403062f0301140d081608040b0a0206150f0d02 68
    0x1440030f00c0803680044144d041429800c000065507401c0082c03882d005441c1c64081541001900c101c0302c0e20900070404007030301c0b035400c82c881540aa641c1540d4200900c11341d040e82e940392440a03002c501f180c1c90b2103105100740e0701c40300901e031149074128980d00b01b00c0710540d100c0c2d10b04c80018008240c0c000c15042800e1750903522139603184010107080d500e805041c4010759551240601c04d019904518560f101a14840c0d103a000b9680c0f2084100700219021600d0740340003a900d203001c140384500c02d0700400e015a01a80c0b074030080d000385845180c00900c41172852004180c03202010420001c1904e403007802050003c008010461403000000e40b82d101e60310002d03200070b855040070021104d0f102c8a43c502d9080854035589840708881402d00e29810034480e600010000c600034800601f005001c120445070700c031101c145840350b000803210f5104404903094030380e201c2c14040495802200b800a05050000b60000c0a8030720b40b035070407090004007000120703000b44650f02000d8410f8848021205001d42d0403101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 627963947 1250 627962697 627962707
    0x30711040207020613030f021318061d0f010c080702120d050c1c0b01110309061b0f0312040c090b0306060f01020c0307060c0c120512070219080102030720030f 70
    0xc2882c001c52440d510030850204000080040d05081119281c0c801e5030b18400d81c04800b940d0780101e600c241588003000390ad44200c14009070302503000c4032082d4106104034002c40308200c90300b840c02d19a444080c41a039551106402000c0d0044e42c81139001c03046200401c2c0c41ca04181d600381c0e076030044048054641e034071000800c0702200901c081d03030081d01e82d00486040300074800c05520050856010130303a012035003002544650340c41c04011551807003c05040c02e40b8052007140c1d44203081c00c900c0e04903a001c1c0110714180e55210030520040003404a00310000d00c4900740340c05c243c40060b150f6440103d6103890b0030b248880d16100810101c3e8401c1f01160300200c8046000010f03418990240007e80c1c0c18010700038003290181d001400c5141860103488a0b0404a8441c49541d025284907200a40306074001d1426803030f0411042e000f00704c00c510140520700b14070003456078601403922071b0704001c3c0540d401104211480b42c1c000c4541012824152544031203a803007103980e603141e20130203401701d58607200018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627965197 1250 627963947 627963949
    0xf07020a0f0309050d21032007050f030403140f01020a0c080a090b032802120115090b0f03090d020109020619090f031101020d0504150c140106060e1203071104020702 73
    0x2180105005481e401401780781c0c0c0b50002c1e0820400b08048007a0080700880d1140510921031000b250303d00a010355002d0054181c1e052180d08842d104890780d114200c60846032001c01e00160000f0341c400c0c502840c0e0340010a0350b890030108a515091520b070710510440190030380c00054441c04542191805651340c0d610ba01c200d0f000320f41500125400d20000007800304195490250300070300300c045491211044610000441070348900d125403e010b900c0c07180188001c410b000f401000c60030345400d000707236010f0b901c58007900720f40c01054914424550200406c030349000e003489106000e01c0301c1c2c8020030820769244e0009000c1d002d800201080c184026003140e0456005110b000090090301030750441d010b54030318151501000c1201043e006014a01c6031a6030340740580d040d2010f840505000c0759040000301e00850b105200e0305026a0020604440018440d01c28410390000e4140ca03503803030101d5502482400900112240d01c4415031344100500800302d640f5500b04035000710101d40259072860540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 627966447 1250 627965197 627965207
    0x70207050405180109031e020111030f09070e07020d08091609020904020d021c0c051836041e030215060103200306040b0406030b0414010f140901050f07020a0f03 71
    0xfa16102d0075860300c04d4200906410859100d0001101c018540508105081c00c038261540c60940d01c40008060010401507842d040203d584400000111407840f95505c3d680001d1070020f9407003501582089000c030920301d500c0380042d030b0302c06007140040c5850007280c40c10205501c2c1c0c61107000035003130340810312100942c1c6503011120402100300065441d6611a0031041781d0000d401c03000070384613140c0318001901c03600542c10b45680901942e15504800607136414002c2c00c0c0c050900502204030800f00d014815029081e621014414115409840e45054500003485007448403444001e10b08084002c40040d500081c0040041c035402000a25030701c400005034042c0009040c1e2001240e40302c00710322101c00b5a40040e51042d41e08503400c0c40504c00c4941880100d425901014043c03044d44d4001030301083d01a000f4142aa50000c0000348170700345a0000003c98002c0400e400e0708a48000c24010411024010650004041c505a0209050078032010395540e1070380704010036102005e201c080034503002e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 627967697 1250 627966447 627966481
    0x1a0f09060f03190c080c100507031b080708120a2f0403050703082502060403110f04050c040302011115160309080406030204030218040c06050c100c0503090d08070207050405 76
    0xe02d1003050b00701d8035482c1181130f2840b21700402615202d40039600f080d0307240900080a25030301c0e54032418a0151107440c1107840084820070903e441c2445004080001c0f4101c00034000c140c01200025261030f07516098001701500034107800080d604203011174203181e42030882918400307000404051410b01940310308500b4080c41d4000340c55400740036030003c05e0001c010001c250030503401c11441c0e651080110044064428136001a4006006010500000d0300e080001611001c005100041903101c0e48000f41c20756000300c0700c0c1da0000002140c204210758000c549071210202880150082a4a21001d01d080703d2004040c00c0b04031a0200e800c0410b44d001c0da01910700141c0109103190350760748911021f0040e6010b8071040b8000c80f02803064000032080040340a000711f40c409a881d100518041c0c08036203d40110300c00004d0f5000e280c443c856041c12500c290508190984c6030140c40386020141b25081150483e0f081003030280203410001074550204240080d14421a400941522056480740400c680 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 627968947 1250 627967697 627967723
    0x90a0b0a090e03040e09060705190e040e01020a120207020319020111010207030e091609060807020111130303030612080904020318061e0c090f0f010e0a091a0f09060f03 74
    0x10304804060030940c0072000f1301c2990002c60000300c140c1c07100019039564800807141040000e83c140200800d18841b044910341e01c004034038200c01c101c036601002800711040c130414241d80342c0d8001f132701080c496040100c82120402c41d80d003c500345183d03600485e4841e9449240b111415810607450307011607008031070181038403082400031911a511460080e0030111b544829620410007100040c419881502c0034131032034843e41c0c1d1280415481c10030145c170700400c00341000e01503540f01e001c0300c90317103407401c1d4090300490406c01542a4650310714100078040f20303180d0b04141d40c10326800030440042140c1e0780480c1c0f0210415200140c2d2980c0da1164001e1012200818001501900c014001000c09585411288041c04103842c01e0985802d00320040134071680d8119908000c0281c9450440d140082c40709026443c181801d000014800c030010f541840d0355005001410358685030869102d0707000255100da01c00990b000615124104000380200741c0c01018284a42400c52881ca01520240120050110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 627970197 1250 627968947 627968951
    0x6030f0605100b0f1e0f0a030e0f0111271804150c0507050114010602070e04020d050304060203040312050a050d020c071a18030c011b0602040b0301090c1d090a0b0a09 73
    0x813400744d0451013680040345030508503040000100c3d990f61024201d40010990031100342c580314030a001135014001e4188218001d000e035190600c04414207010310141402c03002d81c0b45a80d0030380070541d0740041d1a0020400c40c54048610101c089440300c0c140f654416030b01c01290b141030340da2480c1c4480051442c60354100014100441a4081c0307401c03801900c1e03440e1084000b407004611320f5849501101c0c00344956001a4850a41048030100c00003c0d140c010f40042c207061001d64103505c40c1d51940d80161b10003401a4070005041082c0070142d09810b00544151900601d0005580d43c002c040380142400303600b0036940001c0212070520b0421410006103c2e07030341c0707140110070780502c1420240c0107100080c2c03214031390140a50702807602180e0810b05150503103420000384002c03510600c100c080c0c41404c880ca29400c03c0f02082440c51000a14003c18031410041060b51201e04001e01002209030350344c0f401440c40443d5a107540e220300c080c580c090100100001d421004000003001280719a210303046082c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 627971447 1250 627970197 627970207
    0xd0f1d060403030e0f0118290c0c030f0714061b0f010609180f03050f120412170f0c0f070b0c040503071211010509010c1a07110106030f0605100b 64
    0x1500504200c03c01001296221910000340d0b0040d071303004211042d520007105c034000c7c0901001644051a0f022812a005860f01100194905600039400300c40e881c54581e00c0350301403001b20314040084c0301e880b0140300050440d45203404001c100345100005150322175003000c10000d452314070149401030100b0111088414031103005030b402e80240b441c6d000e0f1148607030502034a0b0341f407061585284103074585c2c0480d550941500076202100c050304400280c030703044a410032181c0e41d5440711081305c5001c1e078004c101a000c1c204003000050300c1c1c0000c0e6504425140c0c0080e081110b0352031242c1c21140d10005040304d0a51340d8455004041d414450104020410400c1038180008003808001420603100c041c1c0480d00c880d03486102d2501609600200100b01d404814901007442d4030a074003400021106052030022845160780f4030042100c0d84550351404c00040c82000456944135921007400c0c02c0701002004883e0030368441034078a00b64800c2c0074086a45910200f602480ca28641034002d01640b10001d4503a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 627972697 1250 627971447 627971453
    0xd1406041a07020309010e040c03150e0f07080405060f07111009021e060406051804050108011e0519091103071e1d060904110907200d0f1d060403 64
    0x1100c04038200d203111044210005202d00e00010071680d0360007058448400c0c1445000400000c5c0040c495007104240c2c40301c1c0d083d00381d11025102c00000d0072000d0a03200052800b9907144440500080144041100781020f110100c0d4010690a0708143c04100b0320b1000d40d5407450075101c402241c0761a4040348a818407600e18480c4550040303d8181c400c803402130140c0c02102c0085a200030171252030354410f10400080080a003d0b00040104c00303441d031b500029150706080001c0c2180c000740d00081d0a41d440d00c2c0c0302282d8201078483d150407208488030801c114207100700150702c00c0c261302141c0c0c2002c0e60b44070030a80901850003030070858910000c044881140c4c890521920b0326051110042c0083d02414000c90010000010482e030345142c104c002c00590383e00c50402c40440d0001e0415206c10110300302814594840080711b034410900d94840d80c0820405818000c11010803021059150300a0b6540c00c2507540d00c000740e036502034010325000103885100c050364080c07481a01400b50344160001400010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 627973947 1250 627972697 627972713
    0x70c020a03081e2209050906070c0f0812060f0d05060114060c0a050706081b180409052b0509031221100f050105030610031e0603080304020301110a0e0d140604 70
    0x11300719080c005401299510001005d80e041070320301c410181c201200083e80184a00d1404030003e00645d005950340c68240c4035a200c0c1c0c0d11240100011050031810068039040c06e44110000003425a440d0300d10012a842e03054980a040c0140364000c0c2e4503c142c84055654002600e0702004034805440b00001d140ca00030f541c1b20254850074001c50b418174009207440c08000f000480111030000b00e9460000841c550340b00c0e40d13200080300c80e84182d603100031001090040000c84180ca00d010b196552000e015109400b003664000001410440c0422401405450124142910301140f103005a2503001c1005110700400098007103078030105228040006200d2558803c03011520b075030044c040d190752070703400441e041e00c0300710303401900101c0c01880216100d00c2644041141018a10901036440840754940140e039450351040e5068500807060006524081c42040d01d5030711400c4401e45001c00c5a10003620702d5400050aa120b00c4002040c3da0034425541030555090b400e513026148203180030302e00000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 627975197 1250 627973947 627973987
    0x60f030902031009020f0303040f0302010c060608010c18050d150f0b060304030c020f090c16050c1302180405070c0b060105120f0406051008210702040c0504030b070c020a03081e 78
    0x1129a89124034140c050801004270340079900040b035011107550075a0015501c0e00b6442d074007124020356507000064521800e00c40c0ba8205511682c0c0c40e541d418103010110191001a0040b503c81c007142140c0000007080c100c0f8100030601c1c0b5040c0858035001c4445150001c0c00340700c4181c0d41041001040004165000080d281014400c58640d207050040d8030030b00c510544e0880c3c80868a0004100c5000040902c0007020754682c4a00c049411610110740131500c1b403800248412500c50700400c4142010b00c20701d840d070b4039805059600700007030b1074440070042a040c0c0c4104045c0401e40900c5c086842644a1802c0340c0c1401c180840000780340c00c0c45000300300d0b1460201c070203950f180d10307103004140302c00c1d0031f43c0c0400d040764440c3c002001e001c01580706103685007071201150349002c00d080288100503100c0e03010380e2440300311720740718142c4662950a0400607204020114810080303150741c50f8006941e0142048240c03504103041580347d011801c041c44a0800ea07010030000080042003925400d11081650b039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 627976447 1250 627975197 627975199
    0x40305010501290a08040602161e020901090e071502070e2d01030b06040f140406050117061009020d0f1109030c0909030403141609050f06010c020109060f03090203100902 75
    0x24128180c10f001051a900514414000181480300441c000c69402e4000c0d00081d40c80c20682c1040c0d10381c6558418018098050044c3c5512600208200350f2a103411554014200050b00f8407003100440c49890b150b01060041e80260340c5403c0319090018400c018420280881d00140c100c0b904103122160301c2844040710340100d501c1d40c10b05196101c544c1162290403242c0c40010081d064668800f0032002e07059241c01c035803a143c0d40302081382a03140c144060034041e074020400040d1035410002d0124200d03a40302034a00301a885030090185248983c40501c0c11100b8100005031115400020b0002500d810100449920305042400c014546558014035040104800300c84020300d88000703204070305404803081c120320f030002d000800c0030800e06400045000c00c118281c406003443d20350a110070000a410144026907280100404800d144010701d40251003402c1504010344540d00007400d4400b40d010f403504201e030040112503414003d41180012581c002c1c191003220301c26154101c02001c0a075802e07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 627977697 1250 627976447 627976499
    0xd0609061202090c03180105250207030f0807060209060a09150c020d06050c04050d11040606141b070504140a050f0105030a080f2107020d02010e21040305010501 71
    0x25024081c00369909a159000d0454859542c512015075104e410013003030031766041c0c00f850b0215003542080c800da510480c03001a010b502007210084402030b1200c80115442554840354050001c140601401d0442e40d5100c0e10700b5a6401040c54218060b004045070786030415008503108812540100095041c0c0b5442400080051440c00040f28110300034040607400140c001501404507265820444c3c0c054001c8042514003559040031908850500714165140341e00e41d80d079002d0710700d401d0203441c006002030b00e0000d03400316010f041007002c1c0c8290f241c0300b40c280202a16075010500148044001442d00404c100a8011011400440c2c803004550882000303150000150300030042403965816a1405001020143d000b582c507890b5541c0044026000c880d02406144403240410304c4003421013020340001c2c0028141008080d20380610800321030190b9040c0381c082440400c00241c100d1200c0b984070090140c903100041c030368096205581005c0c101e0b5003044004120800c201803c01801c03060000c1e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 627978947 1250 627977697 627977699
    0x160806070f0305150d110604030c03140d1b05011b0504080f0607090e0712050a0e010e0a030f030b0f060406050a02070f06020601090b270702010b03070e07050313080d060906 76
    0x208400f03d500803541c5507460080e01046800a04140000d0300c0564451030b08040d51445040005c1c03590740041d0700407200d00b40d50100620801090025406140d2200d4009241d0b01c580d5400251002580460302890070081801c4001442025004942c103190070044490078610340c840024050f030300034058281c1c1449807241c41e1040490000f4041d102c0c100c10f5898010041c18611b8440340340b1409042c02c01000380600d009200e201941c460b040c011407001c1c0b00060f0301d000081103282034443d203050303a443d0707900a0400c11020a8001c0ca00e00c2c840b001d1450001110011030300000d000385100702500e50080b1b0081404a030300307600003008050300030190b0211760800366140902c48040816028010040c0c10250040088001d2030304007000318200200b00c0d1014013454007400340301000142e030701c2110484203018031184940a206540000c0002e6020b0321105080080700b2207401c4000e048801002000800108441e01b040d01262a065002c0e075020b030f4420b10707490703c1009054507016030b03d00c062030325034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 627980197 1250 627978947 627978977
    0x50a0302091f090e0f0a02060f0f0c0706020a0201090501020105070c0b13080d090b0c07051b0619031401050411040e070302093708100c140403030917010b09010902070516080607 78
    0x240c0315506ca500400343c5241079a4665061440d801410206448000a0050b40038549092056101412450303008200b10503050000404090341035000605591515051014507984004d1085110b80c06c01d00403030107a1561800c40318651451035000c1e00c81440840d40201d035072255089910b185009000080003610358202d41501881088030013030150b4084803c3c100d28062030b00d819911194000e03d5903041c038000c22541000046c24145060000341c2d5090074035061403122400502514050380c0810141c20600854100c52155000301c440c0400d0850006c0d00c2203220303030100c2d40181c0c0c019004031403895051128038600c0c0d00c400074400c00559040c1c101c1e00502030042d42c0e68200c0c0c001900502c04c000f943d46c118070040010030102402c016000d0610303000c085005000300300944c4070fa5600307502d031443c0c15020441001c400144003126418200e00150310340d1041c0c222811f41e018440016922111490710501e414401881d030b0f6050134a58100003210040428414407442158031481d8550b41d05c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 627981447 1250 627980197 627980203
    0x3050306030c22090c24030507030204060903030e04060b16030801090902210705090907141f120e0601090b1804020a180905060c070201090609050a0302091f090e0f 72
    0x400f0808010001c20510b0b00c42215500a22110360103601d041d000395480303183c030ba611542c084000f90102c030306400400204a078580300e00c990000003403408504050804400500002040c80003404011462240080c559510b40c80b64000707101a080303840d50340306000340183c004a0b0700e24003580414081ca00020300501940103151200768010301503d248041801201580c0507808000915071140c40c0c40403d4980340e104805000d503100800130001145410b2184428a24008443d80914507440c8001404000c10000d202908060306040060100c1415843c5c000d2423800d2444c016442401d0002405000341d41c002c880d1010700b03550880d640880e481f2880b40142d13007600d000b5084004803d0400070803541640c80307034803846030340300101d101a065113540e0701c3d129084d54409074054000803190110768010000400802c02401c1503aa014903001c00548103040920019000f200e4038400940c048912210941d0040640901051b86036200c0c40920000c00c03903000000540c0c81407001399000c0384000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 627982697 1250 627981447 627981469
    0x5040c0201060e4f060e07050607080a051e16020108150f090c09030a060c09050d0506130215030709031103010209090105060d0603020d0515070302040b3403050306030c 74
    0xc8168a00b902c001c600800134540042c00c0344500729404203014140703002e9a4840c0005001d8040400e54840400015040556a600c11407041904002a01c000303405107003650199041810300380d8440c0c40c80030f40070b1890400205610520a4002000031140070107072401145107000384d840c0403c65035840510b6528800f900c0702d0950011101d52560f1a0380340400456502031305140d0042c2c00c06901002013881c000050034110381c40f40d120100d40c1402640040050000c20301202c13081d162190750384916403990b2000e0a41c542104c82c00070300c8415034482c10384800c03080103c00082d5030381c0c2c50041c070010042032042c0000c032610484c0d008201c2c5240780500a44200650050968840c0c2c0d1807d000c22000b58044bc600c8811b240d22400300001507600c442e414403d03580654003401b40120300100920241e00010510024984184010f00035681280f09440040c8015810504035030b124204441c3c44e0440005102e04082c035501d0308400705079008020b50701507030302074088805207140d84040004010030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 627983947 1250 627982697 627982741
    0x302130b03150d06060914011a0a09171501030503130b0405060a030504020d061814060f060613081c1d24041503090209100513110405040c0201060e 65
    0xe0b09000100d140b40040302e200c00b00d845031000140c910307915803041c03041d0b58054034454014000a00104108801c0c0740f0701c2090040f05020441c900200000302402e1200c56004d24030650009000d10f490030082080103c1307496510b8207001700d1940c5e481c0303005640c940c000c4030303c0c0070280d01c1220002014803102c4290350580d10300810080c101150000210b0052000030403e90784106111414800b041c090710541c2c2c41c032444c0c0c24810210a1042c1842c01c80c1944c4268082c04aa01074000c1003840c007050504250000c00841c0c2c01a41e6041003240036801175041d070401e6143c0e008158840c5001506070b1410741044500b43c0700d441c200c030683c09003403402c00c51031050580c00a8007800d801903145145450079100801c442c0d0300500702510f440c200403019599544800109a442440c401545000700e490f540c42200c0c001d0554205041c00c000c684c0c0c851004810800003a110a604841c520349882541c01501014104004281024100902811452180d06241d0140d00c1c0494990800d0507481044100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 627985197 1250 627983947 627983971
    0x3010218010e24090316030602220b1204110414010503160f060e120d0206061c11060a030e0619060b120103080a050705030d0f111215030f0d0302130b03 67
    0x15240c0c4810796181d200c0c1c2201c0361700d80500c1414808507211050800e0196002d00001038481c80d600b0060815801080007000009005903420404803c00c0411240010000c15542d03403a91a0f510b40240c4a910514a55a0240c10456503041450545e000181280c40403400c44084140b034a5028085030b00e81d0091030000040b001e002e004844c01081074510802c4c0151001e4151510340080700c0c2403103c628000001030300100180105031030b0040030200b0500c1c0d00f81c03060100921540c0c0f49110200e5101c50140500300124109104030b000e0303070202d15040c00c1310b01034030114a00707020380c0e1040080d0040c1d1480741c1d034900300010590015450545480050070007500556074215111030003250010715552080000410902d800980284082e004800c000c1101242c500d0901881106580860303881c42c204d88070610903842c01440201e4400d810118030f003403c42c5808031400119003418228003080001c1d10480007640c03c0d140d4075030f00402540c500c8400c91b0000340c1d125400510580b00503280d01803041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 627986447 1250 627985197 627985249
    0x604030602071b060c020609040506030a0f050d021002040506190e030a0501050a14060108181002040b03090f0c030309120705120a0327030803180615010318020d0b0a020903010218010e 81
    0x9c2002c0e40515080310004044510390311160b9221003144000d000200c2d001e4003c4418011895010048049036a100c5072041d401c0c1400c11000c10040c0c0a94034260600b08244105001c50a0298500b80d03001c0d6000f4069900c0002c0703504003c1d000c1d007401c3e204020442d24224084001e4040030394040d005000580d105103990b2146861200b05070100440e90040c3d01070240c412403050501d10040c4000c000c41c1c035500e0b4417450004c16071424070064103221035564000d0011505655400300445007808000c490200c400c014400940d0324040103600b00c2a0000045a1840c984800c00588804050302c00d6483c011404c440b614074032840360010100c1c0038108045441030001901c6180507541c05880303541d903010060b034408100c0307242200907a0010030b6415030030320380d0200e544c1c10301810801609c00703040c0d1704120099078041041c41020300700c0035201c44901008200351052540403500200e1000b002907448200004c4140ba004600d01d50090119401001c124124103086140c4840c407551800400005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 627987697 1250 627986447 627986449
    0x1e040f030b09010f020301061d042f090a030c1a090a0504020f07021e010906020f0d030e0703050709050f071d0105090307030c0b0705010b0604080c010e0604030602071b060c020609 79
    0xc031802800d41e60b0740f03549030b0711021120301070f0744003035402880d095840a0a0014030702d0030010603145000641c3c00382e403c000d208400c04119210312259540207100100c030020385a0080102030060421081e4030000b81c10000041c08407810f0135009070780050210000885030303044424094802c50b10f00b16008042070300d0820851820794040c000606440c040e803460528540c0c000760107604021901720042c1c040d80000c2205590040d000809486140000c000908510341c42c6580e520710008010109512640c9132840103c0c04c2c042c0d0340055511404030b03001c0640750100c10010306000c0301c1902c00d94403404006011743d0321502c0c800d41c0c0e10a440d160245080e1284004441a5100b242d91580610a9801c00400a2038100d4088001c0c4411804d040c0c88080c6841c0c050300350364150406600c5100140030030b115a407000b0800d00e00c078850034280741400d4004040480c03030350302540e4009030040b032010a5070340522404c00790110841d02c80116a080c89031322111706548840800c2006900448140b15080b09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 627988947 1250 627987697 627987713
    0xf0209040b1f0f0908030d06080606060c0601121415190c0804030e15120402030f0a030f03241203080601090f14040e0105091606050a1e030b151e040f03 67
    0x41200b1a1404813280c40c1c55518803807950f8030103070280c244655142002c03c40c03039030203018141e08003208032400c138544009404910780ea4481030061180703408042440304100107042d410001c0700340001003600da4405400613104035082c1e0031219641d0210502e401d42d00d100c2e02c0c910800340c0a0b1450f494200c134681f0349482c11201e22800c80803003600314600c08103d030b5403075000401400002100700741c1500d04d894544189802e02040420184150b4840842c1800003038004000d40441d82d210719000403070307130703015202c40c0c4141072058a00b90200049050125028079013109440e40d5901a032220491611002d004480d50030341d5200d01c111007204d4403014030581c100221950b0700c5010003840800c00300f05001125084440c00ea5065009034042210b00d0100960740061800600c100c1c2003583c20112a528050300320401b100440d07480d400c1d00440204218025444602c103a08050184580f03040310b049c0580a5520480603042c030703403d20300c52483c0a890414220f809031040960141c0403070f0b14555554070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 627990197 1250 627988947 627988967
    0x1814060c03010e09010f0f0204030c05090603060c07030516030c0218101503090b0a140121060e1c0917010504110f06040909060c030c0c03020d0815040f0209040b1f 72
    0x8130654907441031600141c41e900070007035841c181060050342e41c2d10710b00c2d003282c0710326042d80b0880c041c0c9000700421031315540c041542c2c3d0b4020080c02e41c00f0f5880429140881d030511071032000715541c070000c220100905034013580a18030700344241c80006d8030a018a0b0700d8102c4507421a400c2c4500351080c842400817140300c12407608440001e04003c107011005584400c1100001c03207c4110346aa203c10782c2c010015120000f90041107240f20826100302c140c41e0b9001011050000600003549810f900030040c1e8081004980c03c9581055050f45280c400030010042031051007411140101101e03c0381507908184561401241d100f0805c0d0000d08003c81400000d880c01500f040c2c0c0075005110010b00602280203142d400c5201d06000283c54140103005000c540d480d00c0000200820b41109000198000440081e44540c5084c10b00c51039560012181d00c8100e01400307a5041424110204446a0f154020340583c51b030883c2c09100e000356000c24400301032014070300f60484000c8002c0f1503d405000307101100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 627991447 1250 627990197 627990211
    0x821060a05150d05150103150e04030503040c08100902090105010207050a050409110a06030f0c0e0906090a200d181211100204081011041511101814060c03010e 70
    0x64103103901124850308131001201c4002420440050100a0b507a05110316180c82c0013411441e0400c034209100000c1000c001480102030000020111b0f0034001164903580042150a0440e0040c0080400000c090852000c5c120b000d0074030364002080d20b43c00410444251080038140c1e14166191004100281c03210b8441543c2e8410f080459039410382300d50701d0800281100ba1400302c0e241c04624820012150f40400d41c10400010015100c816512051042c1d00030b1000c1b211184036480f019594002840e03030b034401204a00e4030213016071080c01214060000c5d81000311003017148a6036138002406542c4240c03001001c030f00c80b4006000b0000d006086450880c000c0d84122002031000720194001c03a84560406822540185000c98529505024290a061011500b242001e10301b00140356001055598032040c403000c190031901351007040122100f5001c091006028480580c4a00c1400c140c4a840a81d07900141e101039040c100000250b46024550082c110307403650f0710309945c00c00e818101804039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 627992697 1250 627991447 627991489
    0x9010e01051e18011706010b030c0702010f11100e010609050103111219080d1802060a2a1a130c090c200f0d03110f03060604120821060a05 61
    0x343c0e600140290701d840c060400207a40c246203c0c0002c00481c58118164060a0194810420461580403501c00d0360415682800c05120031846034000356031440c10402d000100f4801c95021b000441c0c0a50448507081e0010402001101d840b003010109a510900019200544046402d80182483d424407002c500d030301c20607108a40120a400c0ba000b00040c0e1040c0c40441020429807500d060038410b005000d10b025854141202c041e6002c61214001d041405090100e803c100c0b4900400100d2001e0700201c0c01546201e192803d0300d04201c00b4014003e8800000e0381910024908a60740f20745000000d42142808202c03130300e08070000000d4100ca0884408014001d41601c0541076600c00da0402c44104001408400e070842070010702e4020200c40ca602010b09100151420b4070ba080300300c4850303c0440001e9607480d42c0f0310010400707070310503075200540301c111112180047c4108200a48055082c3e080740400d208a110a0007000742c9080e51080e03030001d20030350200014a000d0403030000300010540c80c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 627993947 1250 627992697 627992719
    0x1d150d020a020a20030a03110c04090c0303170408030f060d0f050a030e0f01090e061504172a040b12160e060301020c0717030904020408010b09010e01051e 68
    0x2555059801040400c0e026901c49240301c41080403060542d07454074003007000c0d11261029400083d0750380343c0c401e40140030300c00c00355514454140309010782d200c1c042d406841801100d00f1458500303255000e0384001d90001d00f0403041e00f00c0c0d0f100c2c140300b41800760750060312007402c6444501581558160103022035503c101000703c030300009048588106203007070141c405840c00020303d0601030800062002241d206141001070740344241e030404250781c19106906170070780282d611000400e4610307070106000d041500b008580000c500d150f80d191144e440c68030006072040c45401a11000700c03004080500007401d105ca83e01c0d42d500c0e04182e8400c103180c010082c03009000c41d00d005d030814201900c000d4551200a5001c505010000c1c1c45850b00d41c10050580003180b41c00341d100549034881d40c4038000d11001100c00c0f006c11400c0d071000c100b5980002c400400440d0741c2c1d5130354101103000b00442100c09000d91266000010303490480d40d1258125000030b441011001c080b00c180400131240d29600a07030000f04185 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 627995197 1250 627993947 627993967
    0x806100908071802041802030a050a050118020c01090212071d040f0b10030b15030c031203130f0206030a050603010c1d10090b04031a0a0509150901020d050c03010f05011d15 76
    0x11b03008840c044501ca0040c4d51b400c1903e1800f0545030002e042c980031500301401001000c3c07901300124468084158011b031540810756003140540384504000c2d40c8041c411a50600801000c2002c0045421034000e80c002070500389001da4809030219405481c40b02c0c000000008241810a020303403054100715800d060649a648080300b5050940302d8140d01000e42480ca18241020005180d41744000c400501c2c901040039584010b034880140700c0301c90100c90250800400254161380c41807030b54002c002030f45a10303000420348000c003011100304e0320030b6003060561543c0600a40c55035028504607050500c0d031049140501c80e0fa40b0b080c502d4031003001052400024586c0042d000360019520496660002266040c00c01801d090081d007420941450702e41807004800000620880c061503101030740c4e04540e151340f9a640280683c1085501d458180010840c0a043c0701c3c1c0114141c0d03142402800e45d05841d07500458071511403001500c810b01070200da01c010b914241303504220004001c1c1c5c60300c3c40c0c111041c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 627996447 1250 627995197 627995219
    0x7110105090d0f020303040c03080903030d0509060406060506070c0902030c1b030904060f150c020d060e071503090803060402072102011e0b090f060303130303080610090807180204 79
    0x124408100e400490100b84041e81c0041224010409440218114213007a00c441180074824800108000400940080180c80a00c2901d42060110100b000146011105140c44020498003110b4440c600000416039103000401d5890058005408600880c1000e20020081d80040c01c4020303005401d0010034804050324140c01101d04240024548801d01b00341400281c030015007118a001100d004103010141c400d045050802e201840d1038140d540c01400443c200c0c04200c0000390105081c45080c0104a80000707100d01241c2c0c48410f840510040110118110303416850002c068180410115000c2c0c9000e8018002207070040e205540c60044004418509480c9460070001603511041e0003981e03410300c0d035494840e02c074254400340600c12050300003a080d440b00401980f01e0040c0d69000c03801e252010000d40d4155440142036812442d03e9046c00b0304140403ca51242c4110001c0703030450312061056010104603282e840042100c90704100341c00014500c000421544152709000c0080c240f1414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 627997697 1250 627996447 627996451
    0x6050d08070b01090b030d03020702040204090e0f060601050a120515040c09060e0604031203091b0f0306110c0604171323030a05071a2a0708011a040507110105 70
    0x80810560300c101518101600480c142e01413107059141c00d0356a44a501e01089140b009402860300696aa0040c80000d0080c0250703041112414a01120005ca1400004000c1e00c0e01c1c603940102d82c01541c507040111054850100c0600002d1000c031248001421181c12290f007082416294080c0b0419030380229085400d0000280005044903400b0020190001c07080300e03c603030b02035406600d001e0441d1510002c281c09181d0007001c2541d5000c4480c03d001204000e5000c029043c4c8100d104640e982e01b400080c3c0350b4602080c0c0304c241c0743c42e0840c10103460000c00c0702d01000005000d04443d0b540e94886020344000801c00303001c0903100300302a007809a207806903d805017003034455007620074000744056101100881802406680710243e0480440c1000820364201c40300d070341d20035680c904146254001c0f40644130f1050200454520095084c1d02d0300588001ca4044c0b242c111003c4560352114103081c1c1c0c1141600524030403c5801c0040a403c00b030708016840320080c180080c4881441814a01312881 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 627998947 1250 627997697 627997703
    0x3070203030105100824131410051219051204081f20030703060906230a060c02040506010c0f03180b04060503011502010e03040b070c0e070503040b090106050d 70
    0x4000700501c058609000041220030003464803420900d40101c104100b006034442480d096000040303640f245541c2e58200040550007881d00780940801245144101c02c000c0c3c1e400032030044144004101400d01d11000a94030880c1d0300102103003402054004640c1510790415221409488981e2003c01310040003030000781000d000800056044420715140581b15060346002c490800518400c0c00084903491000000790100c41c6603a920790355400d500a0180b58801c603460340c07c0020000780000284403058020801207200c41c0c00002000c01c0000d148410300410000c41c88880503000542060760119034045010f06003003545202307545511007800200603003180003540c01d05a052440f42412100070051084c0300144d800c042c1071150140130780c041405402941110030700800c03880e0340300750042040c003904074068035522502c54000c84c0b425400383c08244c82030b2034803d60003c0d181d071606084512482c20750f51968110344460762580001e400c06020444550740751007011669130750b004c0d041501c4501c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 628000197 1250 627998947 627998953
    0x9050a060e1e060609060a080601051e1b0705130203040204021b010b030c030d09031b0b0a18060c0c090b030f010e030a1707050a050705011401120b060f210109050102030702 76
    0x226034010811000b0300401450240006208002e030381d864910541d100240725042038800c2c0d60300d801c0125010301981100803800c418000248200782d6185000306102c082c81480c0484640c40004015500c41035031044503040302d0040401c2842d90135507400303150414801880503203090541e10b021008580010034040d21750355161010302d041c0c0b81c20008210703202425800390200706403424010f000842a071102503c8802d0960075a0804180c280e1000094003074081a0340e262080d00e44014030a18001c1c0d951060206407050214143140941d520150050b403240541451034101160f0001034841d0380001d03078140c4aa4002d0114003a4203005070f900d04c648107002036455030880d540040100c112100d100d2204d240307070400d0112240e03202007141d01820780e40c02c00700e03074031045440c10314014840000e805140c0c4408034000300d034901580b400d070708a15004006910140d242e10302040051044e600240da484100c03011944510032924401021500042c0f00024400c00b06031280d0b82642d00854400005030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 628001447 1250 628000197 628000231
    0x1209120e091302030606130906060f050901060801080705010c11092e030b010303080402011205070203092b031808060c04030515070f0815100f080c1309050a060e 71
    0x410001c0507554866a0420382030b0070701d04107801194a0302c4d00a040b05000380e0628840440c00c41c41908001d4050307511460070407003c2d507a00001c0c016587e450090f54820000c4c0d03400010201c3c860220309040e02d80b27a80180c10b002d403404005480c035004d2000b0440b81c11130340c040200200d940e8208072034410a07100c08043c00c113032038030301400b241207080201c25100444210011b1020610009005041da581807c2001c45c60320303940016160321411841503a5060309040030480c03429404005459003180c00c0e904005c1c107080c4100020141d07459107030070740c4154522080340c1010a1140c9401c00810144c840e245481c140c40b4589030b400c0607403c803100c002c02c1c00001410010410100544038007510b01c1c8600d1072a40c01c00300402484a152402003d042241d40808182c0c00a1840c07014030290303000602d080e1034140b6180740988482042e003100030200d020a000288001c0c0c070402110f10000e14007440e044140c2c10200414002c04010302074079180d60ba141e00c00b1542800c02407141d80614035052514000c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 628002697 1250 628001447 628001449
    0xf0f0603100e0112081801180f05030c0901050d12110d030636050a0609090303051e091e0f03220602011a0d110907050904110909071209120e 62
    0xd0341039101c00c49032207070701380084041440c1e001079908100300c039440d104420f8001401210307000d2005806000024550f5400141a0040c4004804541d410740a035200e04946804104603403409104490f004500314408500048580c654184801c4a6080000080048581d640c1c5008522014880442d5498905011030404540700030340d0920440b023814a4100c150310003e121810951949642075190404602c1c80e9403142c01242c0a410070700d20400140f00035040042c080c01c41a1110008010580d40c80e400c003031171000d036240c442c544e0744000300180484803442c1d0b500e151524000d107001d0700070f080010403551001c2c800ad160b900c40049840c5903040c0310260500088006910100a581c542403441d101c01520721081d103d48401118000300f01c0b202803d14a840384248802143e208089000308103801f0303081400f81c400500140c2e0100a40007026003200a80d1140c030355450b601c0a60f0000243c6c480340f00e1a80118000d51542000c03030030b0606a61203c020f85034020300180424000004060b0b5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 628003947 1250 628002697 628002719
    0x5070801091424040c03020d0b0118060b0f070507120309060212040806151c0605011d15040e07030c03030309062d0c051b0109020306061503060f0f060310 68
    0x100d01d0180b02070030780800b0100001c1051140ca9400c521444074502c00501440403d03100440110b03000703401d0a0609003140303010885101e0900275500e280c03003030380520840c11001d885503e0503161030780021850a1400c03514861190800c000c00c564900c2110008104003210a0007086018030a8803203007a03460034000d001e828050016074401d8103650900c070401c10000b000580310b0b004400f21070700c1a00b104c100404104c04100c0410390b800c1080002803075000700407843c0c2c0f0081c12030303418420f184c441a54507a07002c3d0104c3c2040c0c42d08181020b80c5c2160986a1070035030300c40f080c1d5a10800441c3c58503903899a45043c01c0c0540d5005602295503000400144130150160b0f0f0b96450050802c02c91450010720010211404440d090003026a00c00a50098501820483d0012200040410b202222008055020703200810040340079005d41408541c4e54103140143c071400d5200c501100f07080d659074000380066102082c090951050202c034204800d0b072501c0b03008601030202e9000b003110403401c044403041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 628005197 1250 628003947 628003973
    0xf0c0e1206060d081207080105030705030307030206150307030f080d1506021c20100b0609010c150902090405010b0102070608060607060b0a03300e0a06110a0507080109 74
    0x1008051200d42408844008201d00d988458210f80e10b8007030380349900306112240910050010140394210038072070400d8101d82c03158100c1f42d0450480e100079031a1014541c5901071504006c0260f03011902048e410948003c40720031660340541280c004558a07101c081c001e2103010b400b507078403c01c0040e804a000c601800741000c0480320ac080402c0d428a0301c14020f41d5445e03000d40c0081401001d041c495a580e01c01e1000040ca0302d00c1e2440000082480c140042d111905072214980030f51802402c160f060500805981280c1c2050719040c0e1880e00076100d044200c20f0030301c440c07041d50b41c0d1860103400580d611101c2a014500480000800e0b81d510710001e46000c05c140c02c9102480314443c1001303103580e03a10086074191903111101141c0251000042500440c0e550001000c4200c1e032031030140d00c00c100b22103680500140091a03005255612420740721a0f00c0110026001003241c0000d000c45800380861940051600f412500307444595101c0c1410131165801141d0543d4407500608140030452000c60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 628006447 1250 628005197 628005199
    0xa08180306060d020609042919080a2603010605070b06011e0c02010c0503030a05160e030c010806010c0b04240b0d0209060d060606021c031e050a06030203010f0c0e 72
    0xe2908101000500c6040302020081c03041d54005010146ca80325500b000500d1401059410101288400703d080038031400c03039025014211007280c060b040c0760115451802c071124140a0649039a2513111503071401421220650014000c501c980c025900d2000114000e05043d900c8544800c0a898401d038000c2c0b000c0d02030b41c100001c010528111214091034190316001c603007425101c4405a200607140354055001c094480d010100c02c1000981c1e06810041c4104030302480074041009082041e40c400031003508440d05548151341c40c400650107029020740003a0141030030060107483ea9101410b48404403021a06170301340b4001422410b05282000c144c50801e02c0083c070040a01c24049003406099003006481003800c007001c07a507644c55a0303241c00300c0950010000c0c0310854071640041d40d01c0b0b01c050050b90390b4002181402180511138400d0307080a80e04a400c0ea0f03102c900801e91540a4034000e400e0400315a035071780000006950074416940d400c03036070b5030010405d512151409009541200109 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 628007697 1250 628006447 628006453
    0x30e03010c08070e0a0302030f0a0b0609040b0402010c15050a0902040507140904090c1211030706080402030d111612021e100c050313060201090b06010f14070809030a081803 76
    0x508041d60444140c03684040180b404003a0350903410001114000c40d5800690540514141442c54802c04150b2800960140c80b00c0c40762510384c20b0038800280d200f01d03001340034101c040012400561007900754221890141401c60320404075400c12404465064a41050081ea600012011414036020315984210f2505008004280800f800c113120b1007044a00380c0f2035941d030001c170801c100c000140c801c0607102c0444c1007210354820740fa24003180c203500706403107229200e42c0c0c00000316280305182d5541b05030b030301801810240000e130100f550340c0325040c0242da92a020b20300109246036200740d00c8400407c840040164031102034011b102000c1c4584083c001e04400405604030f254a4110540c040703c082880c1455401d142800c0c104c0c00c2d802101145c8484810900c0000b0f07490341d054001d0705180d4011201442541c44110064508807400440e84004c24203000d00d0032040c01400c0301810466004014852602c501c540000f8105075841d00111a010300208580d0700e80c030103030803800041c00425802 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 628008947 1250 628007697 628007711
    0x1a0c0a0c2606070c1b030c0b13050f010509041d06160905041802010c030c170d0c0e01080a0902010c08030f010e09010207020a090504020409060c020c19030c05060a020a050d0507030e0301 82
    0xd002c51241c81e405016488003a200084a17440d6441100c0219000180c100107141c0f80d24294009500c0000c0d00b28020110f89004980c51030000c80020018a0503107400d890701da203020500014050424005c1580c08400206201c8c4840512601e03101d64018a0341003160003804c00081c00c50f20b820b40100d0f009038581032250008080707030380c80200d0994090801c0211b6280c0e91804036040024074400078500320424001042800b0200f010304100d0603c8542401284200701d001c43c0e00c4c0300720780c00903800210540089501c109881e408985210b0061410f03051450003915000b18680c0151381c0c6004100c8070000401ca566042180140c1200c1000000c1d498580941c0024a80e80010301941d80816030320400308085640d40e1b4403e40c0f90650180003441340444804010b52500d03101d81c0314901a6840f441440c009241900e01d20050301da0080031140303214107002c10300c00c00d40c000b60302410a502c50101c1202c04504100901d0141e99402c1d0349955aa00c81072030b00800304d04510303d8a60085e810024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 628010197 1250 628008947 628008961
    0x6060608190e061b1c090b070c020d0b0c0d020f0717192a140706031107080703020a050712150203010b0909060103061503020405090108071a0c0a0c2606 67
    0xb0b100f580082c400804e007103102e01c0d0204040740b280b14800e004d5000200030100c000c0f182d20b2070b4119182c8030740500c41410b55640d50360300c10340e094024100002d5014010b103070002d0000c0c411000c1c4079000071107600f2140c00d200c1c0078104981203a10800460020140120308034081001d0255403042e188140d941c40f5080204000d9505400c4885000c88014449080f03540003c10b01081540741810382d03102d2819501c0c00341d07801c029500703030406101300340c4500801030701061840c000d002c0c00c040c0700d0b0042d031040d00d0b00c074068072041603e8200300022421402040400004642c1c20000704004e0488401a92120f804522b0000c420b100940c224a02d014010b0004128030608039081c0c882120301901c05c00310307580d40d00c0c0040340203048039044485c0e4440c176030b440c0901c050340c542d01800079600b098403513100700d03602c54941540d210864401c903901c031a01c6481d000700c1d400300800602400c0e07034140c048500c3c0d4140d607a55030000360100d0f008080c2d1407030000403200d0341240d451003180d4080a120081c107081e042040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 628011447 1250 628010197 628010203
    0x4020408060f07020a020a180b060c120c030f070b010f0905060a120c26060604090819090510030207030206060a0f150507080a081807060e01120906060608190e 70
    0x40610350b0070032808000035242c40c021300030f18102d141d0040c00c0d100c2e4540c84500030b070300503181c0c040c120091074504420b100d86070910000303c401310000003000b80152000728070400041c0e132103000b10691070b0000b44071074005051900c0213844403902c2400030402c1581030030074242c1c0311055a07000b48403603801c00741800080c0e103515a88106483d0344a100140d20a000d08183c00311440c5540060510b070120809010030f01324a2408040d01c5001d02c042e2400d585441080009176155144064101e4008100d000703685240c20314580101d0f895030401b400d50a0f61000004d00da52100411000070a4000036441c1c2013507418000342c0d030301401c205e5105001a0500e40e03610880b81c9580900c0711705015084a100f0041e0080013030700c03820b41e2302003101a95544075000013400c0503020760301e03961440586030380440c0c0e0007804204a010344580d507481d1010081d00100445055100040075110688d4a1000d407011491901549014100c1c90300d40c82c02e503091408003460420740105030f240d00945043c1c80c80050042c08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 628012697 1250 628011447 628011451
    0x309010e0609070f0b071e08030901140910051009111905132102060c0f0d0504150f0e030613150c0c0807020303210403080711030d0e0f031305030c0402040806 70
    0x6143d46c3c40310041c5ca045000300309114140090000c3d954400c1c07040080c158011485682804006d00401c07440d200004040d0000381c034071000e181c008a801d400b40501c158001544008151f0403910015a11102d0800310f610b0524680d102c1400019045c83ca00c005000040c00341000e0310f84503107030401c4800c7e000c4060049000b00c4507220305524280d403001c02c250507540c45e565001440303541e0b1440341c0d081403942d58280031502e000c280540040c80d284580124141d03002c6542204400a0403c096401120801e5400540310180542000d034035543d80c030304120040c0704085a91552928055500780040d003911601c0d181c1040d9401c04002000d5583d10030145101c90384e0103e0003507242e10051001a0075801404200700c00c4810380f4400360b62410b80c2090030b90040d40240c80b0340305591500740303040301e9111494242c18010791080003a1030030008641e20070311100b40c03010140c2d01e60720300ca81c07404c82c110741c89483c404040000d502400d01492600b4040c40181d4182150214602032800000b19211303140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 628013947 1250 628012697 628012709
    0x7021c0c08060133200f010b09070807030923010c030516090b091305040302070603050703140412020a080d0204082401030b0a1503030309050136170309010e0609070f 73
    0x750031641201580070301c040340307141c100c1483e0f0303031002582400340706aa0b0012600002180e60808090400500b0189c1180d406511640e07140c103d169107510095000d41101d600c2102c0034212103210b00040c0c2450f008642401052000101f411012640e0040071742d0400341050031480401c081e80070405401410390011200c080340d401d5100c040c0000003a101d60303a0443d41e20001c504010030030040590204981040c3d0b946d94908200b580c441000403001c0b20421300f07610b0140140c03e070101d004a214a29441d03007510315032040701c0d1407a0196499410a8100c1000c032084560048bd090080060601c60368103500c420140000c03c28000c0707404030700100340c10f2202a11061004c00400d010b4201c41d08008924070150060011040e40c91800034020013084a041d0b4055280c0786405803025501b81c60f00241d1181c2c4040203540c0d2070740011240d21018140c0c01120001c281a0101840f40a003602851042da14200001000c1c8000c514690400c10002c01d458001c0e044010b00340540305603e465541681c0b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 628015197 1250 628013947 628014029
    0x810060210110c0f0106052106040201120e1618140a0908120720060714030604090b18070f06020304260a14010b0303070f0807021c0c080601 62
    0x20000b0004000e612a2140b03200d010700554844001307141e4150800000c50341c2c1a47c458061840440d60400e4401e013144a122040d0000c4020401546c81086040e1100d032540c1400209aa1000c201e070b46010002c080d204108078a0039420000c0b165400719a41c02c0d0781024006100202200c52080c402c2107004008010f800d58441c10390040c80320210a54540e0265109070748841d00b403180d0042e00050700c041c03040144400c0c94821190720400803a41c0350003003515407104d00c03600121074050401030300000c3c042500700d070741c50030420040f03030303800462600131104070a060100b03010341c24400b410015160055500010000020000c85500000300c504680c50029100c80c0310380070000d5856400400660f11203103109480c809400c1c01096440203400e581501c000300b004d24120300a142c1c41e4003c004001e030520710411a2000824408001005d0043c8014003510080c4807403040700c0c10800a0070020344800c5000c3c81c00740a005010803445014020813001c102c0c002106060034156511203440000d10f0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 628016447 1250 628015197 628015211
    0x11b0b07050f0a030e010516020307150e0106140909070e010b13030b0108010b0102211c020405040e06070e01080f04030507060f1803180b250209160810060210 70
    0x141c403480a032100304a01c500030a03561030031800004c002e080e0a42510b010365203020301141c801550040880d01642168001d5420400c19803a802481410024500c01c0709484141200744c004080c072400001d0000d41040001041c4600c0912000400041a14156512008061200c0e904a041d10b90440e00c40038019550b6005210140034aa0340c03540c002030039103020100110b003034607040d0840c800158080c3c0c200c5414100c081030818220101026000800004020302c0901401a211110b5480300c004400342c5403654030400b250440f4845107441b0000c0d0484400c0c0401d046e0301c0455050304260074680201c541c02d121000c900d000c42c1c041d1005060050008031581000b005402c01b60300250242010032080401c44030390303110b080400c074040b000290450607848000100b400b1007801d0790b00000341d6505046082c0440c02e501d00c5080301c10303203a80181c03241d08001a5202d03512288a403041100d100b035070080302c1d60b0261106902802c0c1407202c4015410038484990f0003e03440f54400d000d08008a111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 628017697 1250 628016447 628016461
    0x30f23010e0a090b1e060a0b0a050a020313083f0901110703030504090c17060402070f0b0709031101032003060d1a27032b09050604050606011b0b 64
    0x20003809030f000748509503c00411840d01e07011190900f4604008075103a546640d10010000c103903546001c0c00782540c01c00c1c40303000d50061140c0080c000c1103115004817450540741419400256905503c003050560000103204c0c440c01c4014622a0246018a4480e00103450902e03516602520100c40544141c1e010401da0340300d0f8408c0082d03041c41c1840405403a01240c1340e040c001d10f10380c0140295202c06080c4002d40b00614030030740c20341040e400d04003a42045900c0d48402c002c040e6104840035540c08820142070804100900c440310b00542c2152a4041058910f26002c010b0404040c2e00c10f061516150180162072030032003440c801d03015144005d42da0380d81c42600140d01b407504410054070300f50015001001d06a040208580146103050721662555440a001c40c00780c040d2092214054000380f26217543d005440b0300d5201301f40e20b00ea105015060803144080c04440b41602c090712540e01c85400d20091010910080d60064030a20340307800706148125120348001da51460061048001034002402c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 628018947 1250 628017697 628017701
    0x9050a120c080f09120304030507140604090513030228020d03230403051603050a02091009060603020d14010503070b031012061a0306070512040f06050709030b010e06013c030f23010e0a 81
    0xb60420120800182c101054341442000360786001b1009446240c01d900040c100c1c1400281010340c0303420340510140c19942c240880d01c80c200404800b80103d480d5568080343d80264040302c242e215181440c1c40300e184d400c01c24a00381c146d01c48040c10b0710709181c0600100e400407903802421030b01914481419110309001186c2032300142d100400951815101003105507140d002003621081c0c0c6541448522084807000b0400102881110381c5a400b0513420030001000c0400345520048024100c506190764090704034100e0080350040b942190348080c2090000300007140d0458180003640206940e16019601600c24402c6010074451002e80400160400c9181c0081340380c02d0703500c200103010f00d040088005d08860325a000c200c0340c1e135008200204101c1003440b07145110340c8050b9a440700500101301a03420b020020304c4160f546240790082d04550098000c19070f44101c030103980000701080105110011612000420921000b40382000c074511400c8541e22819580c500003110319130340741c40c101d07400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 628020197 1250 628018947 628018949
    0x390d0c0b0a050709123e060406021c0c02030a03050309100b06031927050f01050c090f18010b0a0e010201060b0d0507050d1109040f09050a120c080f09120304030507140604 75
    0x1041411445501c0e449050540d4541c03c08a00070401405400e1b103141001805e008501035240140e2100508410000c000e8041100354841070030000807410a907004203041240c1100e06402040001040c000d030314508101520340c0d031980340020400640100c0c00102c05101c06000181010003a0403d9080b490640d805004442d907013a004e9440c20380000104071320a964505c0a450f28010030344a6040b402040c0203c921030302c106400a8a040c541004200075245800c10041e040340c0f156442c2c40c2c02c1808004401c1c060109100e8540c0c0320604080c00800440c00842001c0c110390415004000440c6680107072052080b0303000700844d4541e22080c08036880c4c0030700d401405070346003825a0b20705a20081402030040c1b00302a03d040c010001064000b41c1035400b8503800500c117a1000520002085201c2d50075946503007240340c00c1c900104103460f0b00720203400080305502c1e078400c00680e1004a103070600e0342078001741c2c0c03c0b40554141451330300d40507120f1a1a2007600c0d00c4402042c20b5040390b903104000c80b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 628021447 1250 628020197 628020233
    0x10e1201020c060403020d02280f02060c1b0a06080402061e0409090209070c0b0f0402030c1504050306130201020d1101060518040506060402390d0c0b0a05070912 71
    0x1502c2d912800a840d58800080e81c040d0054015041013030301da00d2001c90140c600c104110038222107a148454001401e991510f001d840003000e001001c40141d58583c0142540c5d4000c000030301e40c000300482c0c00f840d4024a0803050340f044460001c20400c4940043c0040d5215130100d440ca900c507913501c1310040c0d220300c038121000101440080e020070b03280b0140c3c0c0090150750098030030100b26078074074005035404c0d584448090440e242000c00111608040503032036a1140c400f40659040203030748400708801c840344415510000304007080501007420100310442c0d01030144105403005140355000070703443d01400c4009400f0000a50030b8000703903e000350808001801c1c00341407001d094007400c004a00c44c2905940c03c503550b01034540402c070300e0324040c0240c6000c20282403140c0356041c0c0d070110845020a0f81d10440c000c56244469558230f6086c01c3c40f10511000140e21a1400840c40c0c2c507042c02511001001500058070b03007400d000d0041c0c2c0c42949081543c04c280c95021405c40141092003414030603000d42c2d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 628022697 1250 628021447 628021451
    0xc040b03071205060708160806120c0a09020705011401030812070309080d0507020607020a121b0204050408040e0f0705030106030e0f06160201060501030b0d03030203180d030c0f1d010e1201 83
    0x242041040c0004c003d0301c10f400d156030303110f10b540790300031200b070200001c0701d605000503c0c45020503001c1c83d0001c0c031710503003074020000c0780da100540c0030100d4482c0516901c0181650f9022030072030f0030b101c000c0c0103075900d244080151190a60644d074680a0300d00a0046040c1d100c0c0c0c52000060119020350302180c0c0c5079401c920550b84a0000c06482c0e400b41008a941030014060f00d0301240340380b4000682000c0503a801004240c2c0b640034508200e54888903144100d03451800201c00c0c0000d40c50320301c55030740a940942d031403035520f9052030700ca5403d842d0027030074140c8a50000d00030803a045038040d003900d064032094a804104c00d030065081901c0c0880300903040d00f0354003075078040c82803413404a00d0040c5071a215400a1040d199190010f50844508900b12900b1401619140e0006032290b8002c50788030a0024008006403141d00c01c9501d080d80315025040408c0d6200351040c0c0107a001011000c0031101490184240242c540001400e0701c1941d4509060040b10105034a440d41c8000209130400e0301a002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 628023947 1250 628022697 628022729
    0xf170304170c1c0f060e010605090c090a0501082206020d020c0c100e010903112d011407150c110a0b100608010b12071e080a05010e06030c040b0307 65
    0x18407515400050742c2640b08428150030002602804114469100e8004481a00344200e07515208080c0940c55400c80d03080d5071743c40c400b10f00c5075a906003060042c3e076008080c80c2c07104820410b1200101c02ca07008030f03050140c11010803410a403004082c07200c01880701c0f4142c01035030843c40c1c0380c0064040d11120185690000c02c45924203200096007101a80c42111401c803119240c00cae090f10412800c1c3d00180c0011000c500600204a01114030140007402038003030480ba1071021243d0b06001c1c60003e030041700c0210400300444540e40b004c40e0480354042c5030003140c40c0034126550003034004100102184001d40310a500041d40380103034080300550904a094070400005407600c8604004100d6400311200030011001ca2190f201e103880303070b060ba114230040500c1e1801000da01500400300628030350403c50b050500000984082c2c024803003100c1d150300c48510606001000109444c03050b0001d02d1200010010403910ba0750001e840d01c1486401e440000d040c0c540080070a080102c0c58203d10030301441d2280c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 628025197 1250 628023947 628023989
    0x20d060902090f040e0c04020309160f1a2104020d24060806101e090207060501050f010f0503060103021602040903050a120603030c02120a15020904060503070f170304 73
    0x5141041040703c030b262000c0b091408000850742c01c50700000880e4017089925405042950085420010500c103c2e44a814050040f596081c1c0b03035000492001d140c80d8080003103813020a06820200005a0454100b160142ca981d4004003c080d4840c8007130980c0000c43c0554403055200c9031115000943c529114000c0300384904840f00010728402e01c00c2ca0180009180e640224000340205008446c0302d21051812f03859050004294440c403c020741c5512002440600502c001d1100511400c0c0100785989008100b04100c110400140e0601c5884a01c14504540c00030071a41d020409007401629041036002c070b02d802d10748030340300290800e00d01121001070541090103400a480241e869800c0703412881c10010980e0741030b03c4020b0200c5c01100c2c180005103000202c9642c01e50210084503d5407566480d80c4000148a5014180b55980000e60b407000781403070300981d0003500d000c0d0300a1504500d003007294018105603100b840d00719044448081d10f401828001c5078010a4504500400d40d0640c41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 628026447 1250 628025197 628025201
    0x911151608180411120c041206060509061002101e11071106070b0103020d03050d05151311031504060308030405150117060417190e0a060206240103020d0609 69
    0x401002c0015411041c020300c0d1416004900c809040c0c2401c20b801c10a0038104200080c202034640c250249090102043d5143c1040d200d00b0780314011500881c0b11880c00307040c46100c2c800070300100d004d40b040100706085150000b403034600e0419080b400041d810840d0703ca00300e0800641c81902516420200100310305038050025160044c041c0c00d200100f201e03001c0c01c001403840b41d0f2100070140b4000d000100090b20b404640d010a1500a082103480c04482020542c21140115031214400c4000c003909011400c0c03000664200c400d89080802402c060300800c44600c0c0801442c0d084000c030581c1030100c06072a1908800029917110850750380b00e007080c2c5809034032854510791110448520600020720014980c0541001c2520b142c0035103815219500c41840c80754079050b0520300b8003400c0115103000580c0e244408c10030500f903555007052208203130030040d041c8100c0e4040400c55110b41e043c84400c91842803a290262001d001404e1003158034401a0060f016122005040034030b0303d0700006500d1f00036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 628027697 1250 628026447 628026457
    0x6051002011406100c030e1503040615080c030327030a08040e0a140109020d090203160612020c121b03030124030917070804120302010c120911151608 66
    0xc011080b103541e26641030003d5980c0710801e500c0090b4126201d1804207018002442601c0e5025054130907042031b2180e036061070350068608454440e6038003003403201e9030304083c4041c0190843c9005085048540400256a030158400c2c07000d00044100008241c0c040b0700c04450a00c460240030758030907500d14108501ca40d002482104156012580044d050780d40d10700c00d2280b40c00241100140590030060480c0c0250080c207000e0b01e04903030300da070340c00d01607541084010710f035141c218070041009080c000010240c5501c51404030145006000125a070000810004c04540c52100c1c0f40340c84240801120391500c41d5000300d0801c40c040000042420001845400010300150b807034107401c100184022011034031040c00260801415980c1d559545491070000c19046014101c01e42c106131311007020b820040841802180540e5686410500d820b4104e20640c1404191000c1001140410f4440d07116200902540c07500c00c4c04c8058880380c6810010042e00d40390010390b00d04005582c1c8918151815501c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 628028947 1250 628027697 628027721
    0x10c080708010b0c07030218041a0c03160c1b08010b0901080a03050c1504061401081b0f180a0203060108011505030601050306060c010905061b040612230703050a1505010503040201120605100201 85
    0x250b10300b5007064040b41012640a0064443c92f40e166503104400b00341542d445e00c903000704002d10400801301091841c01018541000b1800700c00405180103159400c640301a40c072103002e030000400400002c07a01003104807a491b0107007400f5542d20720841d13596003401c40d00608500c0f424126414401409915440102d2500301d0003103d0302241d80381c0311410360b40c0c0e0024207a1509800c441c0800159800d20034400f10a8800107091442131490030175800c44140e030100c48103e506580032041000b9583d209640c0d038010042207400c43c401c0910108014014030000b4807080c14072a000011803242d80b5000d044581611410000b088481361903c0d015807240015181003910b01c1054a1152404418100b05e03001c035001342e11741880e00c0a032950b40c3e80c050501201107003801c5101b00a4140b0400000d0380e02131040550395400100c07460003000c82000c48a41e02c0c10013040803190902480b160b60002d040300c0e001902424090f8104140c500070401801c0e680c0c01090b000b14200b400700c03210b03d805420059030409 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 628030197 1250 628028947 628028963
    0x24170109062c160e0a08060a1b02030a05031b0d09060f02030601210905060c0d060e060603070e040905030f0c061f3008090102010c080708010b0c0703021804 69
    0x82d03180303180d41140d000d200a2400b00c000010a80d07442100811012154081c141020304030740d07030800206121025800540140c00040420080741060b20a1000c80421059a05d0f11404d0004000b5528003030703e20104180900000800e60040c010340c0c031034003401c40b0000a280e494103280c0340203002e482145400c032581810035038802080201e80c007e0364400c00042c2c2d03075104010b5403a000411500b4540d40c042c80120f9862079800089a821f0180c103118000d050651030350f8480d80d403401c1044680c66884000c08194081c14000c9564403d4101c03a04681c842c0b03000740348103401e24006401409a290010000e01c00083c1070341c14002c0031805450702c5515a02036401c181e5400740c0120061040c800c2044502d42c0f4640184102c01c0ca40080001d1900c407150b00c040c03000c81d178000710b5550098600007030342e40c0c0700040743c560b4066034240104410105c0328540385010303060103803000d05856818011480d0502d0003081406080404120120096030010300d0094690007025929502035020740e41621141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 628031447 1250 628030197 628030229
    0x902040806151e040f05090c151804270302071d040506010506030709030606120b0a0c0e1c060908040504060f0b070b0a060305060a140603072417010906 67
    0x514261000302c0c07008405003007980740c3c2c00c24410100914002c000b996902c540c3d5031410f05d8121350700d4030445101c1d003504030060024100000070840c21640d41c5c80f8102a0071001c000440c2101c980c40c50b00030208409950100302c0c10b14625188031445c95203503550012003236a0340b20b10b05050b4005038034001c4912140495520085842c2040ea03a58011540548030b0303408040104481d0824100540d0b10112a251001540d0f86a558200a4507100c4d404441c0e20021408088207200080c440b094011400d2007081200400c0d03810041e00030401c5141152107407950210440d2201403480451203c0383d40b104040005807518a0b249201d40c101d80501d50050707180803808649410094856002e4558041025050064030754034540103600052401c4180d9489810010015008210042c042c441011b008140110307002c10b030207280d9400401083c440c0d44404010040e113225400b500460790030310720402440b5207960605803005810160300e480c100788010b00001307a0204a50101094641c2c008a801a80c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 628032697 1250 628031447 628031461
    0x316030504030b0709170c2d09070e01080a050f0f0a020408120c07060302040b07060504081216030c0207140d050f0604050a05060c091e030a060e0c0f030f030a270902040806 76
    0xd103d01c0003801d904000116032841d05440f0b41c846012348208200c48000040228101055134204c1c29209440802c0b00d10200c0d00e2030b90307002016940e0080c0418020030840c6480c03041e00b0302c0e01c440a0175080b81298498007048120714550121000b8101600c00c844581c80142040c51455004c40070707101860180180200d01d040c441d000700c1d801c5030002c068150815285803100401042c001d0021511024100181d440150303600d07910501c202d4030443c0b10b140487d030854010301a41c1014000004540081d03c003444a4580903040003100201a1114103800a5910b08940342200d40440704034248643c00c208420404000b540d050401d106109075007131074544010000081c0030f0404000d03444003151001c40214682d01e40181d82208c1c004048602c0c14000380c94a00c02c0302c0206050b032034590000d100005013418000d012440300d4405034000c0400e86000c92001d42c42c0d0052580c03c50800590950704880c82c14240700d520190351108400100c0540d0f01c201c4c18000394024400c11442e4000d1200140706 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 628033947 1250 628032697 628032703
    0xc05190503030c16020a030c050f090c0d020d06030212060106180b030a020a0339050403050303130224030a05010b0a0e1005070f11010e120316030504030b070917 71
    0x412903000004608607251800c4654180e0000740000c1d030444010251500035030b851406141c000c40c01060040c5101d1b00b00780c14004100c01068520f07014103041c0c000d110300181d402089400100000e140180c8980812800801602080e84065030040e0015240ca50304c080103d0814101d86e007036150074210701c0d290b910200c114042c51042011140b404c1c40060252132568000346442e10841c40c0002e03240c0c6114103a00e010811080c0f4015145045040100d070440c60702e08412000c00702401c04900342884c5a1f90540d81e444010074805030010740e080e00d0402c43d101e4100c040c1d0551183d41042d8082c03892040001c403590000c1318404410340c100000010048d080204580a501d081e51342e820752764030f00509005100c000415202c1c10800c080055030302040440003016007403446810342d4000141680c0005001102d401d440703610a064000d01500b4078080002154605561908041820b00283c01d007501d1500441e070014000908010800000325800054141500c8207070ba1901081e040c50b401d1a96 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 628035197 1250 628033947 628033993
    0xa1127181003120c1b0303030c1704081812010b011d0117100f080705120601121202010219020a05070f050a090b0616150f05060609010c0302100c0c05 66
    0x1500008600c802e001003075052256101888182c2801ca5506807155240c512840b83e4076196185103050f05e4040c020076074140544208400107103085500d924071011030305018180a480245000c00c0001c0700454154802c61460b0b10500c0200071820002d075081e61180a02070300558a070000760340e040b041c1001c1446007404142701c00180e45889610404025800380c540c0f028000003403040c204040002d8514514051002911029026090f039503e0003040c080210100c1d1030480441c1c20440050041d480b00b60140001150000c4010703400216584043c5d0081c0714a0740d43e00d000606400c6000c1d8541d0300060f04488161040049600040ea1040da003201c41040b03005543e8404001201000540481d400854951381c0c000e0009141c030301142c03d204144200c1f88412a101e0b0001c0d0314503403031103e01e03103e401804804010140064900072000468a120b80101c16051150340c405100905108108013039102d506950108002c50142c02c0142925803a08411200e92085016485200800030302d104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 628036447 1250 628035197 628035211
    0x20310090f02130e041a07051c0b01140f04030b0f0f091507030902041503030c050706020a020f0603070e0d0b090c0d02030a0f0f05030403060c1101020a080a112718 72
    0xf041c8207003004083c4945400140003901ca20003820384102c10a13132002c030403030b020341e903603448682d40c4100014100f2000813424a00d412518030b4520650a83d9030010084480559501540d030340e1203907088031124150150307070030152503001e5881c00c015608500a814034092809281410215941c1883e00d41e07a808410544d02000b10b0000701040c00c0900075002140f0840c8024404110240c60b8038283c0c3c2071501691050340081e50799811003003482028807540002d000c1e5440644000c0106401050b852403401200a0041100200081c0c00c184a03408100126500803d44030410660b42851541c0c12415640c0c1d000f28042c01c48140b00502d4803090781c2e6851076016014188000050f00e9103c01c0e8074040790b00b950208007048116002440030300081018500c81c1c3d000250820301c040c0001c14440c1940c0305001c0f26841000f036200c2158200130055488220301501090218407629202401c0c061440260440d10a800d01d05000036000c100900b0106010740f400c1c1080a000101c02e0800d000680e804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 628037697 1250 628036447 628036477
    0x1403070305100806131410050a090204050708071e050408010207050a150b1c050f0f0601080601050108040b1f0f0b040306050a050c0412030c120f112805070504020310090f02 76
    0x83e200403154001c4048413098481400b61f540c81c401c10307540101e07503a035409550350700000214607040c8100340e044007075841c00005901c0c000302c2c003900404060340083c100e1102950260310641c8950100e4001d01074042c001d6407100c040d450895070b28140f81c4400c5a20036040e444083d140001886103d02201c0010700f04140c4107140640310f502c00000c54400e5a090086a1446002c1582013000489012510300101460b40c074144549041841c1070700504d04101c1d010080c00040f84003440305d15002f241503101d0540417480520010303104200c0783d0110320340403880c10002415840d500040d204690096405201d165201038040d4100c5000f11449612843c0c280b20922043e820711801c040340902c80d0900340c0346142580c95200307100e0012400e4400055170f442510741c0213a80300241d4018421000b0081402805400e100065034034007880d4010300740d81c0ca240d100c0a124041124500922024200315600d04011140c84048982401003001107401c2c0804c1c050b203a0024421034085035041c03070705 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 628038947 1250 628037697 628037731
    0xb0d0f1107080912070b0d05010806070e0f18090a060b06070503270406030c24050406030e1009030801170708071518090e010c0806090402101403070305100806 70
    0x1000c00c1e9812616015410810441d1410980320040001602801c94a41e03416207440019010307c0a450050300185896007025082c04401c0d50000c002d46a003607400c48603410000d05800200d918104c0d40f0301201d41e4141904144050040702140803400d0601a240900280e1403002c140103041c46500c000818503402042160124807401c01605100c2507a18107060301c3c080c0004c0000c007620b01d103400c1a03d2042c1b610700c00700000f07440030807500c1c64880c0005444070185510203014010340154446c070028580c5528001401540a100440103180d0b100f10030041200c040c20000c109410900420303071402800f06400c4548680014044c003280c1c0c81e5401007034206c0c14941c10b21030b291505400780082c400e400c0d01ca01c845a04c9200c1440107008165400980340c0f910b00c04c0603080d2044800b0642c1444900740a01800342c8508045a03400307078040c2c46000e000c0c210000c04890601c8404d0540c0d0060401000741f100055050700b110340a1285900444103280d194200c60b40c55480036260010741d0064065 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 628040197 1250 628038947 628038953
    0x50d020120120d0b0414150f1c020306010509010f03030e0d02030307140d0c020a0b030c0708030a1a0a2304020c030a020a0b0117070612150b0d0f1107 66
    0x4100329072142100844010540c1c9600007030b00e00b8105802600225030003142014190743d440c032808000c2c0308211030500c610f403040c501482c42601c001d070413000d02c1481d10407268240d8031410410300c2091809884001c0300c0c0050841804a130011041c200c0c840e0144400004180c60440241c038140c482d80b9030780c466000d00c4c595050f1001c1072803480240d08107c80708a10005a40c040c40944403207801040d1251050514060b420f0402503030144c06c2c0e0030700c0b00d040b4010000da1141c00c8848184d840302c28000c0e590791150b01ca241628025144001c060504c00020803403281c11a8000c07041007618044180d005289400400030000002d006102d22100e030744105401c080d000f00031b00030b8104009000140b070025071130a260300b107900c2850381c01c0250344000c44000c1000b5400c00783c2070040012003480420050300001a98940c0328500c0b40c0410001c03600074594001e0416804180303451504003034103004c1a521848007101d60469810580c0c0300c0c0c0303402201d0039441d103903005030401c0d141c030714402c0743c90500301e55 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 628041447 1250 628040197 628040207
    0x403150e070b07030f021005090307110307030c1502010e060708040605060f030d180f0b030f040c0b120103050129130204090e1c020c06030103032111030702010f0501050d0201 77
    0x36600d9803451040d0100058221100c00051290600a41e40c1d0070201c0940f02c0040d10700a91200c910114501e410100000c481c004400d441000c0d0307201c03403030075140302008001904d01007441c0c1002c1e00003084500006000200c1911100c80303599590000c0c8199000c0010349038403203004881010100d000c0c480014001509644055400403006100a10303001c5241c011911b00200d140c10840801d941001c0d000704d01c000c00800344000c00d4402107401e5140d080c19000a00780c080608100180034485001c1000c010446140c44082c01e4904029601c60f03500c10040400210203100c1070314603500c2c2c008c001905a081800d000c03c5000b06003844422002c0c1d101c01d00c070b69200301500b00e5030081e60034840803451440d00d004240c1115200c20003021000440c0218a0200f07209059803800c1d50301200d140b01703061700c4e90429a411641c05080ca00c0c50f80705480c458070300c08900361000c074806600c0d044e0b5682c00d2038907110185001c2c02c0b044c4d00800c0492a01c1840200310f440a00903e54020420800000107620075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 628042697 1250 628041447 628041461
    0xf04050403030219051b030304080a051c02400314030909090604031e080105090a090f03030504060b03070602061923040203151909050c030a0c0503010f02040315 71
    0x649070041c0f500c000e81042d500c1000c050000000000c90020742806d0448814005035080c441c4180503514506041d52031000030f20904c400321060000120301145d030350611405038501050f12041c01e65548071032440300d0120713036001000e64405040704070040f000c929618801c9840600350b4086408482d0550b00d86083c0c0d4040110618101e20081082c84002d0319050480740c0101416401082c3c107082c645000b074140b8400c0c9503a002d1501c0004096101c0769800100c150465400383e0302202c0c0c60700c41d42d1000028007450b20020340081d407041c41110405515901081c4540c0c0100740800008512900b00f64442c1d04078070801c001644400d0100d88500701e0f01c01c0c044040d004090b0001011220181e81001c1001d940c40c184080702c00010800056060030302c40c448403440501041d4505141001700301c204000d8026046000603a078445c03550400000300020902440001e00b01d030444605840c000303030f8071070140c01014080e508000745086007a10f07500035101030382c0d881401d0384071651242c10354070020150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 628043947 1250 628042697 628042703
    0x605030c0d02041509271e051c0e09060406080d120627050601030b0a0608181009020103060806040f0305030c040506030a09261b011508030901090f050f040504 70
    0x2035500020304c000c4407068001c0040810700304c0450749490303e4080c0407040d41202c0403486036150032011400001c2c4030781d0702d6080081009681c11007101c40c0d41400e52414023450498030791038002c2c0b95040314064201842840c0d403202102c0300c3c10300c3e0307842506203c00e1320002d1044096543c4046040304000d80580c03414115003130f8041d00041c15a0741c3d00301c660066a01e001c0c202c003882450800c40040e401460080c55800703c400e08007800321441c0140850201c800d14031a401c00c0000070360200b8081440003110400c42d40b900350480d50380d001d440001c00000c00c04150100c4c0400c0c6001c40000d11107c000c518a0312a9400242503101403400d030f00c05a43c140c7c00109043c841600c1000085210b0b514500a9401003400740000607200c2041d28200c001caa164003002c10b044100e103d4030301c0e018152981210703c10541c0300c41c3c5040701c456913a40d46014120602d00307400c5180180d00b002c14083c0000002c0c1844203000d1740c600c05203c0d5164a0b0101c0f1080c40d01038a50040d81240c080d43c8181810b8100b141c010348 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 628045197 1250 628043947 628043951
    0xf100209040902210d1701050108060102010b090a051006020120070312050c0d0b0405040b0a110c120306010f0809061605040306240605040506031602010e0601080616030605030c0d0204 81
    0x100e9074001981c00c41c01103007007403040f1001ca00c003e401c0a13042003007900d4070032241000a0780e0011211070759004c800510905041041078800a48240d00c01c4d00800c1c3e965a02130b00c5000c2c1030900e03040c11400b0300411111608640300f0031100291091050003840d800c0341007040c0e019456460020088516480108107030140001c060a56032030031600d11889203c0c480304403459454181c5a2076110640300d0814859204a0510080c0804141c40319085a00100720003800035104081050b0b80c1740c9401410b070280510700560003258030340105100118410b82e000d90781d02074020f0910400780d400800c16120403115a000c1030000c0c168242da401d658091443c0c82c20700702d0500380d4a0783c801c02500c206000900d5030f480e180601d010381142909080000c2c2442e810484d007003c0c00d0401140c19404010420188010b2128a88503c64001e50002c202e8290881c142c2d0621368540341e04698448050382e0802c02e068400040c03a04081c03082c0700f0f500940d1801400f8044c48a618001c01a01001410060780c0c0b00d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 628046447 1250 628045197 628045211
    0x22104080408030c012414090612010c03090b0c070c03030e0a09020c100b0909030706092102030a020d080708010e09120307171b04030b13080a0804050f0f10020904 72
    0x40b410805841507644400000c1240c400003081c0c00800c40d000f5680e0081804101300a0250f001403040010703050400392510f40140d5600c4002505800c0b106003401ea00b54604107503110301c0755041d04018441c40c000c0c011710000d0b48680c205292a4440c126000c0c1200610100c1440000d00c202d03a082c04640009289201c0300341c9a0b00171400720383c0004200030a03544000c0c0c0100079016035010f45103441c2000c030380c9280c0915040f8207013a1a0310400c10010003c036520111041008810411078861006100c1d0b07140b0942404040a940d80c0d02c0b480d02c01000d8407600d41907844640c4200c003502c0c45484981d036042500d03440c010961110140c00f030301c68211400f40081800c0c0019558002d1072003080d040e610f540c2c1c11658005441d0072034001900803084540ca0300625144000140c04441c203c81c1d01c05052112541c0d40d141c403180b215030045d8000c004150010309000d509a214000900075405103040d500100b02d4161040c0d80e600002074440c926030044a41c040d500c40d01b5501800c0c4050000e88041810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 628047697 1250 628046447 628046459
    0x140c09060c030c010f050103030f2c03030705010e0706200a120e36060603071112041d0603011404110414010806010e061002190201090b120106120221040804 69
    0x980c5d5403004c10580260703151700410074140d01c03002c021501c4800c1d05280c070081e00b0f0a43c20540e4120807200c06160b0245080400d00c1130346080080f141541c1d0040c001b01700801c2d40344075041e283d12052080e40700107140441c203180101010100601d46043d44402400c0c0340002d0781c2d652403013005000400007030007034600f44140c240e19a00200a001115080103540d1440c203071254002140c5080700b13149400401c0010800755403119002c598001915003000740c0c040140c05180c6107000400c0f440c080e00c96201140001d5100d1604d01501c51420101c0961655070b59548185402c07604150a1903014503551008903000c144012030940c065000584042001c0c071644445140c45c1c0420b034080c840348d40c000d40041103101c501d0b14185810200403100c44040d00d403002002503a07450030108503000074480480400440e805201032030001d200c03548805498809507180e0b0410034509109070700124100640c051070000c190300c00caa01d071010101c9040c2065561100442008100900854021008202c08181 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 628048947 1250 628047697 628047701
    0x1f0f060b030a09051c081b13060504091b2003210a06120201050f0307180b0901030e0601180b1201020c0f010615090b03191a0301140c09060c030c01 65
    0x42501c0c002c8010030340101614280b4501100a84d200d8000b0038220b040f111010342c00040d42d500010a040741400044100c0380766100d074402c02012104085146c0c10018102e82c200024004544210400b040a908001e00804503515a9100d91001a803207840e030803545807402141005210350b070002c0b07030700705401040031049400303c0e15120805c100c484800c000313480f0b5041c00b80401034801ea002e1f0202c2072134550f0001e810380c06048030f00d0403c40c601000240d05c4034414543d00c0c0784086442d25005800d9a0380411404640c44802c02c0c500003410584e09050641001440754104c400c0000380340e0710504030401150007030552000e8268400f9583c2220b484040b4240040d2203082e141c03038060010002c5200015084030202c0d0300c401c3c10710524815440c0c446401084683c1225a00000140d41e50340b8200a0740b1170030a2840c1200d070b4245130494042d00020140400b000900041c2c000b08420154050b01034100d070000c44500440315010001c00000e802c1080140c1626100081100d0401c0d005c0c00006003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 628050197 1250 628048947 628048951
    0x5120f04051207151d1f0f030f05010b03160e1507051203010e091006050d12031e050a06050d0c050f0310050112021503091011091f0f021f0f060b03 65
    0x130005d0038a1240c100050208a4032a003040c6040307403100c40b4002e11041494600c105003091105110350f0000b4505081e00075005080b9040e03030040c0810840d0785900e076110340307504280d50b04503100c4517510305107400500400c003030380806c880140000c1d0803406070300a07542c0e26800768008031080d008170380c4151075845d0b004004d98040c1c4807018100485141500089140c000030464120482e0305220301000f658450005468100741c0258040710100c0c1d4000098000d03040c69942c1c40c50411001d015148200b006611280c0144200c040a0100ad41e66404001340c80300c02c104090b098034154a001c020303914040d2400240914094180c420802481c000ea000301d502c260b000d000003007074448003001149803040f10044a0301001080a00b98180349003507035510000602c0343d00e103503659043c000f2140c4421809071119954002c01140b5001a040c07000d1680101c40c050076004602038640d6081481c0c00401c2c581315004000c5590400d40c0c2c0d40d00503800141c04104035840b54203a071900c0210700b6035000d8000b18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 628051447 1250 628050197 628050239
    0x506010f06171e060414040f03080603150109020a021c03090615030b04021011010e010204050f0a030807060b06090a140a060302041a072d05120f04051207 68
    0xc88081d140201c050311180380405044507200807075041158803080341182c1e8402c00c00d040740b0000705540d1480400e0007010315426981001c07030702c8410841049031003c8400c110700d2013680c4101040e1106824940c2d1642840d150b1002c0f10307100d01c01402402210350150074111070314412101d45003014808000c03204444148400040d444214000610449016001c050041c040743c1c0c440d10340c81c68566684410001d04000d00c100600d15582c50524403d1075a407558a0f81d0500070040100c041c1f040b14001c4d8000c0c801d1602610241a60250610b011142c03001101d41103c4060318049140c2e03100f1004000310b41e103140d448103080c0440c15490701d0391140c52001d041c83c0e22031490010075000800402c0070155008200b0540100300c00d0049034094442044040903c040907910703082c651401412040301c0b002001600d280309640990801c041c40d80070101503010f42c040d50380d00d1000f0002c80d07059100308134110310345071802c010802c5a400c0030303038820311610740c400d0644c2d0740305440300c00e081c02c0483c0d9100d400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 628052697 1250 628051447 628051469
    0x1506030705040c020a0b0c0a0917070812040e01140609010c0314162a06111e0309010801060c030207050904052409010e030403020f06131205030301180507020705120109050601 77
    0x104e406c014850314190341082201241e6170425416107070003480041e460088004036a0a4070b000c1c0c001e40300c00c2050401400030703001030303d00d4070801145440287d00a841031007032188101000240c115454a600d18204001030441850b20350700320011344d0f803440141422400c00a108500100d141829806040310100034030a030481d401050418001001c03441246c60546a84021808174041c05c4041010444141c5d00307086203184910341e07505083c0152014421440a000040c03080402070200091440000c2601d5244040e41c07107407011140040e0108004000d60702c2904141302a24002290030b502610850448030036200c080c0c0b0001561400c205190070403641d5406010071a0420300501d140051a20b00450901d407958001410303000d40e655145004490015131007140390388040716540904901c038815213110600703180030396581cae009101c1c401102499400d008489401402407d0081a00342e00810005080008100400d0012403401100d0b660f180c0c0a4000501e0500190b07008003800c2c114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 628053947 1250 628052697 628052713
    0x200604030305160e030a3e01140a120207020a090c111b03070314010e071206050f0408091011010c0810052e050904060306020d110c1506030705040c02 66
    0x890f20b10508004010280140f000080c0050344000613101003164010f25050210320042c040f03950103c000150038442c0c0c0500300c04a100d0b454034101100c10b4503900380d903080300d010300302401d4a8480c000c041c0e94000152807100440d18510040d0080c142c0307280000c103409086035680070200101d891410202020900000c1c5003540c210b4140030060750488109066070151141c2c50000e61144a5800014290a0803d0700585d00c000d0960044055124032000c950f10305480d01825402c02a104408440d031038240130000b01c6c00382411829900483d1f011041c24204800b1101700001d02350550920300030013004201c06041500240106e41c5450750503120781c1e1950078200f050000b0885541c00c001e00407401010703450030b144402403442c950b03a825610b0b401001130305001c086440d441601c40e0f982e4454186003003c0b0501140c1e0f801858546145141088041c00300c25103045280101c5841c010550049102c5142024010300325540c41500107058519035a02c034400141140c0300948058016400010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 628055197 1250 628053947 628053961
    0x60d0c051c23010518040606080706021501060e0d032610060305060d0203190c0b0a090923011203090506131509030f110409050105012301030209030d200604030305 72
    0x1510300107901c030800d81d0850b00c0d8101808591000003000e8079526242c000300004080c4541680f045028201c000103a400c03181da2680c00a540b441580d80e4820b03400303484400061194060441e411149802506e09020550300d42c03010769082c0142c0c03a81c44403542e100749840154825005065100b440301004090110342003042c028102e6200400c1103000f288810b00100150340d0006410703071509028106c016248905241c2010300062035032155120306000306507a58203580000c900d0090703034a00305080209080704020303102584503801a4405102a45005001c8509848940003a40380a410800402ca84c0c0f080481c1d0a0340c00b000e0304151810704408144110a03200c0d0b41d9400100701c1d803a0000455007076443d440e1300c00d480b00000409082514200500a844070b4005000c01034000c0020011f075039550010703d060200c01150303480f0645102070305d02c1196010340b0130348180140c06070040400007449001660201c000007100301d402c0c0c000386140040d2980800461f41719511959000c101410462 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 628056447 1250 628055197 628055231
    0x1e100504150c020111030604270506071e08041205071403120117122b09022d060a11030409020a080c0405281211120606060d0c051c 58
    0x580001c00716410306171419050f0602c08140c0c3c0d0843e800320703400079000b0240012107003d40e4452520106510603403c011080c850042641885024544c5558100012990551818002c802c001c880410607250101c0d02044409100c1001c1c40c4050804c00c2c0b5000c9152075100081000341001404c60340002414007510b446200d0141c014880050540c4420300001152034840345149400344a900003c620840605110300c00703c515140401c0c1160001030444201401500e000700003030b4040c412413201602b4901842c120803801d1031040c1c40c500d00007000203003000000d500180b84d5408105100615240100c070501c0204001d1515032070041e61001e4040001d84500001808a918030005020400554540c100801200001000510131030b20030000513244001c0d41e600b1580c80082e0003000d4804000d40b200314041c50400855064940d0342000e1340d141e548070801c03117545401c1601404842c96104d450340200700c6c0350403181080360414040c8140d031842c0d001074080c440380c01511000c840d03044d80d8a00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 628057553 1106 628056447 628056461
    0x1a0904060314011b05090d11060f0a0f0e1e04021b070f1703090d03050f0d0c0e040e010c0801061805031203061c051e10050415 56
    0x321014001e00e41d4002d0781a41ca01c1c418901c4400d9802441900c24088008004000d44055a9220001e51401d051b2080d08809c06022007941c02031014080c00c610881c0341d442101c84204003000801001074090024040d103840030541c070340b0400d05a81d0f4100c0800a072400f6a40340d4403540010f400d40d951040031400b070f008050003c204203036410041d20455031401c41da2400800650305031a04c034810705982550004104128200003070240c1c0c0903000010103003007001c0c00d1210039440c400959246249c80e40004103c0300e0803000c0c074940f611400904020400c000c100951480d02e0180c00840c060140b0f01c144035132809181c807209000481b601c0a8040036040c3c0310017a030720b0711020442e0303041600c0d140c1c070545003500c080044802090b41100441c2d00070000380103150f42082c14910800d0403080400c424007482c0c614000c0c0d18800c1c01100c0c0190300c141003038000d4031000380d03000007110b8034 = true := by decide +kernel

theorem cover : BRFrame.Cov 627877697 628057553 := by
  have h0 := BRFrame.cov_init 627877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 627877697 ≤ n) (h2 : n < 628057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
