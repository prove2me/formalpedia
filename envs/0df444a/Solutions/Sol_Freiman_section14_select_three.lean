-- Prove2me | solution 1 for Freiman.section14_select_three
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-18T12:09:38.13648+00:00
-- url     : https://prove2.me/submissions/2fd88c05-9cdd-40ca-99d1-3b55b22a14c7

import Mathlib.Tactic.IntervalCases
import Definitions.Def_Freiman_lowerHistoryVerification
import Definitions.Def_Freiman_section14Geometry
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

open Freiman

namespace LowerDev

set_option linter.unusedSimpArgs false

/-- The part of `lowerHistorySuffixContext` that the endpoint development actually uses:
the catalogue word and the real word agree on the two terminal-run tests. -/
def sufCtx (w ctx : List ℕ+) : Prop :=
  (lowerEnds w [3] ↔ lowerEnds ctx [3]) ∧ (lowerEnds w [3,1] ↔ lowerEnds ctx [3,1])

/-- Weakened context-fitting predicate (same as `lowerHistoryContextFits` but using `sufCtx`). -/
def ctxFits (base : LowerPair) (C : LowerHistoryContext) : Prop :=
  sufCtx base.1 C.words.1 ∧ sufCtx base.2 C.words.2 ∧
  (decide (base.1.length % 2 = 1)).xor C.parity.1 =
    (decide (base.2.length % 2 = 1)).xor C.parity.2


/-! ### Square roots -/

local notation "s3" => Real.sqrt (3:ℝ)
local notation "s7" => Real.sqrt (7:ℝ)

lemma s3_sq : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma s7_sq : s7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
lemma s21_eq : Real.sqrt 21 = s3 * s7 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]; norm_num
lemma s3_pos : 0 < s3 := Real.sqrt_pos.mpr (by norm_num)
lemma s7_pos : 0 < s7 := Real.sqrt_pos.mpr (by norm_num)

lemma not_isSquare_of (n : ℕ) (h : ∀ r ≤ n, r * r ≠ n) : ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hle : r ≤ n := by nlinarith
  exact h r hle hr.symm

lemma irr3 : Irrational s3 := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 3 (by decide))
  simpa using this
lemma irr7 : Irrational s7 := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 7 (by decide))
  simpa using this
lemma irr21 : Irrational (Real.sqrt 21) := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 21 (by decide))
  simpa using this

/-! ### Values of certificate field elements -/

lemma val_eq (z : CertField) :
    certFieldVal z = ((z.a:ℝ) + z.b * s3) + s7 * ((z.c:ℝ) + z.d * s3) := by
  unfold certFieldVal; rw [s21_eq]; ring

lemma val_add (x y : CertField) :
    certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  simp only [certFieldVal, certFieldAdd]; push_cast; ring
lemma val_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]; push_cast; ring
lemma val_scale (q : ℚ) (x : CertField) :
    certFieldVal (certFieldScale q x) = (q:ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]; push_cast; ring
lemma val_neg (x : CertField) : certFieldVal (lowerHistoryNeg x) = - certFieldVal x := by
  unfold lowerHistoryNeg; rw [val_scale]; push_cast; ring
lemma val_rat (q : ℚ) : certFieldVal (lowerHistoryRat q) = q := by
  simp [certFieldVal, lowerHistoryRat]
lemma val_mul (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  simp only [certFieldVal, certFieldMul]; push_cast; rw [s21_eq]
  have h3 := s3_sq
  have h7 := s7_sq
  linear_combination (-(x.b*y.b + x.d*y.d*s7^2 + (x.b*y.d + x.d*y.b)*s7)) * h3
    + (-(x.c*y.c + 3*x.d*y.d + (x.c*y.d + x.d*y.c)*s3)) * h7

/-! ### Linear independence -/

lemma indep3 (a b : ℚ) (h : (a:ℝ) + b * s3 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply irr3
    refine ⟨-a/b, ?_⟩
    have hb' : (b:ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    field_simp
    linarith

lemma sq_eq_three (u v : ℚ) (h : u^2 = 3 * v^2) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp at h
    exact ⟨h, rfl⟩
  · exfalso
    apply irr3
    refine ⟨|u/v|, ?_⟩
    have hv' : (v:ℝ) ≠ 0 := by exact_mod_cast hv
    have h' : ((u:ℝ)/v)^2 = 3 := by
      rw [div_pow]; rw [div_eq_iff (pow_ne_zero 2 hv')]; exact_mod_cast h
    push_cast
    rw [← h', Real.sqrt_sq_eq_abs]

lemma sq_ne_seven (e f : ℚ) (h : ((e:ℝ) + f * s3)^2 = 7) : False := by
  have h3 := s3_sq
  have h1 : ((e^2 + 3*f^2 - 7 : ℚ) : ℝ) + ((2*e*f : ℚ) : ℝ) * s3 = 0 := by
    push_cast; linear_combination h - (f^2) * h3
  obtain ⟨h1a, h1b⟩ := indep3 _ _ h1
  have hef : e * f = 0 := by linarith
  rcases mul_eq_zero.mp hef with he | hf
  · subst he
    have hf' : (3:ℝ)*(f:ℝ)^2 = 7 := by exact_mod_cast (by linarith : (3:ℚ)*f^2 = 7)
    have hf2 : ((3:ℝ)*f)^2 = 21 := by linear_combination 3 * hf'
    apply irr21
    refine ⟨|3*f|, ?_⟩
    push_cast
    rw [show (21:ℝ) = ((3:ℝ)*f)^2 from hf2.symm, Real.sqrt_sq_eq_abs]
  · subst hf
    have he2 : (e:ℝ)^2 = 7 := by exact_mod_cast (by linarith : e^2 = 7)
    apply irr7
    refine ⟨|e|, ?_⟩
    push_cast
    rw [show (7:ℝ) = (e:ℝ)^2 from he2.symm, Real.sqrt_sq_eq_abs]

/-- The rational norm used by `lowerHistoryInv`. -/
def normQ (z : CertField) : ℚ :=
  (z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2)^2 - 3*(2*z.a*z.b - 14*z.c*z.d)^2

lemma conj_identity (z : CertField) :
    (((z.a:ℝ) + z.b * s3) + s7 * ((z.c:ℝ) + z.d * s3)) *
      (((z.a:ℝ) + z.b * s3) - s7 * ((z.c:ℝ) + z.d * s3)) =
    ((z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 : ℚ) : ℝ) + ((2*z.a*z.b - 14*z.c*z.d : ℚ) : ℝ) * s3 := by
  push_cast
  have h3 := s3_sq
  have h7 := s7_sq
  linear_combination ((z.b:ℝ)^2 - 7*(z.d:ℝ)^2) * h3 + (-((z.c:ℝ) + z.d*s3)^2) * h7

lemma normQ_ne_zero (z : CertField) (hz : certFieldVal z ≠ 0) : normQ z ≠ 0 := by
  intro hN
  unfold normQ at hN
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  have huv : u = 0 ∧ v = 0 := sq_eq_three u v (by linarith)
  have hc := conj_identity z
  rw [← hu, ← hv, huv.1, huv.2] at hc
  simp only [Rat.cast_zero, zero_mul, add_zero] at hc
  set X : ℝ := (z.a:ℝ) + z.b * s3 with hX
  set Y : ℝ := (z.c:ℝ) + z.d * s3 with hY
  have hXY : X^2 = 7 * Y^2 := by
    have h7 := s7_sq
    linear_combination hc + (Y^2) * h7
  by_cases hY0 : Y = 0
  · have hcd := indep3 z.c z.d hY0
    have hX0 : X = 0 := by
      have : X^2 = 0 := by rw [hXY, hY0]; ring
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hab := indep3 z.a z.b hX0
    apply hz
    rw [val_eq, ← hX, ← hY, hX0, hY0]; ring
  · have hcd : z.c^2 - 3*z.d^2 ≠ 0 := by
      intro h0
      have := sq_eq_three z.c z.d (by linarith)
      apply hY0
      rw [hY, this.1, this.2]; simp
    set e : ℚ := (z.a*z.c - 3*z.b*z.d)/(z.c^2 - 3*z.d^2) with he
    set f : ℚ := (z.b*z.c - z.a*z.d)/(z.c^2 - 3*z.d^2) with hf
    have hcd' : ((z.c:ℝ)^2 - 3*z.d^2) ≠ 0 := by exact_mod_cast hcd
    have key0 : (((z.a*z.c - 3*z.b*z.d : ℚ):ℝ) + ((z.b*z.c - z.a*z.d : ℚ):ℝ) * s3) * Y
        = X * ((z.c:ℝ)^2 - 3*z.d^2) := by
      rw [hX, hY]; push_cast
      have h3 := s3_sq
      linear_combination ((z.b:ℝ)*z.c*z.d - z.a*(z.d:ℝ)^2) * h3
    have hef : ((e:ℝ) + f * s3) = (((z.a*z.c - 3*z.b*z.d : ℚ):ℝ) + ((z.b*z.c - z.a*z.d : ℚ):ℝ) * s3) /
        ((z.c:ℝ)^2 - 3*z.d^2) := by
      rw [he, hf]; push_cast; field_simp
    have key : ((e:ℝ) + f * s3) * Y = X := by
      rw [hef, div_mul_eq_mul_div, key0, mul_div_assoc, div_self hcd', mul_one]
    have h7 : ((e:ℝ) + f * s3)^2 = 7 := by
      have hY2 : Y^2 ≠ 0 := pow_ne_zero 2 hY0
      have : ((e:ℝ) + f * s3)^2 * Y^2 = 7 * Y^2 := by
        rw [← mul_pow, key, hXY]
      exact mul_right_cancel₀ hY2 this
    exact sq_ne_seven e f h7

/-! ### Inverse -/

lemma inv_correct (z : CertField) (hz : certFieldVal z ≠ 0) :
    certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹ := by
  have hN := normQ_ne_zero z hz
  unfold normQ at hN
  apply eq_inv_of_mul_eq_one_right
  unfold lowerHistoryInv
  rw [val_scale, val_mul]
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  have hc := conj_identity z
  rw [← hu, ← hv] at hc
  have h1 : certFieldVal ⟨z.a,z.b,-z.c,-z.d⟩ = ((z.a:ℝ) + z.b * s3) - s7 * ((z.c:ℝ) + z.d * s3) := by
    rw [val_eq]; push_cast; ring
  have h2 : certFieldVal ⟨u,-v,0,0⟩ = (u:ℝ) - v * s3 := by
    rw [val_eq]; push_cast; ring
  have h3 := s3_sq
  have hN' : ((u^2 - 3*v^2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [h1, h2, val_eq]
  calc (((z.a:ℝ) + z.b * s3) + s7 * ((z.c:ℝ) + z.d * s3)) *
        (((1 / (u^2 - 3*v^2) : ℚ) : ℝ) *
          ((((z.a:ℝ) + z.b * s3) - s7 * ((z.c:ℝ) + z.d * s3)) * ((u:ℝ) - v * s3)))
      = ((1 / (u^2 - 3*v^2) : ℚ) : ℝ) * (((u:ℝ) + v * s3) * ((u:ℝ) - v * s3)) := by
        rw [← hc]; ring
    _ = ((1 / (u^2 - 3*v^2) : ℚ) : ℝ) * ((u^2 - 3*v^2 : ℚ) : ℝ) := by
        congr 1; push_cast; linear_combination (-(v:ℝ)^2) * h3
    _ = 1 := by
        rw [Rat.cast_div, Rat.cast_one, one_div, inv_mul_cancel₀ hN']

lemma div_correct (x y : CertField) (hy : certFieldVal y ≠ 0) :
    certFieldVal (lowerHistoryDiv x y) = certFieldVal x / certFieldVal y := by
  unfold lowerHistoryDiv
  rw [val_mul, inv_correct y hy, div_eq_mul_inv]

/-! ### Signs -/

lemma ratSign_spec (q : ℚ) :
    (0 < lowerHistoryRatSign q → 0 < q) ∧ (lowerHistoryRatSign q < 0 → q < 0) ∧
    (lowerHistoryRatSign q = 0 → q = 0) := by
  unfold lowerHistoryRatSign
  split_ifs with h1 h2 <;> norm_num <;> linarith

lemma quadSign_spec (a b : ℚ) :
    (0 < lowerHistoryQuadSign a b 3 → 0 < (a:ℝ) + b * s3) ∧
    (lowerHistoryQuadSign a b 3 < 0 → (a:ℝ) + b * s3 < 0) ∧
    (lowerHistoryQuadSign a b 3 = 0 → (a:ℝ) + b * s3 = 0) := by
  have hs := s3_pos
  have h3 := s3_sq
  have key : ((a:ℝ) + b * s3) * ((a:ℝ) - b * s3) = ((a^2 - 3*b^2 : ℚ) : ℝ) := by
    push_cast; linear_combination (-(b:ℝ)^2) * h3
  unfold lowerHistoryQuadSign
  simp only [Nat.cast_ofNat]
  split_ifs with ha hb ha' hb' hb''
  · -- a = 0
    subst ha
    obtain ⟨p1, p2, p3⟩ := ratSign_spec b
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have hb1 : (0:ℝ) < (b:ℝ) := by exact_mod_cast p1 h
      push_cast; nlinarith [mul_pos hb1 hs]
    · have hb1 : (b:ℝ) < 0 := by exact_mod_cast p2 h
      push_cast; nlinarith [mul_pos (neg_pos.mpr hb1) hs]
    · have := p3 h; subst this; simp
  · -- b = 0
    subst hb
    obtain ⟨p1, p2, p3⟩ := ratSign_spec a
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := p1 h; push_cast; simpa using this
    · have := p2 h; push_cast; simpa using this
    · have := p3 h; subst this; simp
  · -- 0 < a, 0 < b
    have ha1 : (0:ℝ) < a := by exact_mod_cast ha'
    have hb1 : (0:ℝ) < b := by exact_mod_cast hb'
    refine ⟨fun _ => by positivity, fun h => by norm_num at h, fun h => by norm_num at h⟩
  · -- 0 < a, b < 0
    have ha1 : (0:ℝ) < a := by exact_mod_cast ha'
    have hb1 : (b:ℝ) < 0 := by
      have : b < 0 := lt_of_le_of_ne (not_lt.mp hb') hb
      exact_mod_cast this
    have hpos : 0 < (a:ℝ) - b * s3 := by nlinarith
    obtain ⟨p1, p2, p3⟩ := ratSign_spec (a^2 - 3*b^2)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := p1 h
      have h' : (0:ℝ) < ((a^2 - 3*b^2 : ℚ) : ℝ) := by exact_mod_cast this
      rw [← key] at h'
      exact pos_of_mul_pos_left h' hpos.le
    · have := p2 h
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) < 0 := by exact_mod_cast this
      rw [← key] at h'
      exact neg_of_mul_neg_left h' hpos.le
    · have := p3 h
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) = 0 := by exact_mod_cast this
      rw [← key] at h'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hpos.ne'
  · -- a < 0, b < 0
    have ha1 : (a:ℝ) < 0 := by
      have : a < 0 := lt_of_le_of_ne (not_lt.mp ha') ha
      exact_mod_cast this
    have hb1 : (b:ℝ) < 0 := by exact_mod_cast hb''
    refine ⟨fun h => by norm_num at h, fun _ => by nlinarith, fun h => by norm_num at h⟩
  · -- a < 0, 0 < b
    have ha1 : (a:ℝ) < 0 := by
      have : a < 0 := lt_of_le_of_ne (not_lt.mp ha') ha
      exact_mod_cast this
    have hb1 : (0:ℝ) < b := by
      have : 0 < b := lt_of_le_of_ne (not_lt.mp hb'') (Ne.symm hb)
      exact_mod_cast this
    have hneg : (a:ℝ) - b * s3 < 0 := by nlinarith
    obtain ⟨p1, p2, p3⟩ := ratSign_spec (a^2 - 3*b^2)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := p2 (by linarith)
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) < 0 := by exact_mod_cast this
      rw [← key] at h'
      exact pos_of_mul_neg_left h' hneg.le
    · have := p1 (by linarith)
      have h' : (0:ℝ) < ((a^2 - 3*b^2 : ℚ) : ℝ) := by exact_mod_cast this
      rw [← key] at h'
      exact neg_of_mul_pos_left h' hneg.le
    · have := p3 (by linarith)
      have h' : ((a^2 - 3*b^2 : ℚ) : ℝ) = 0 := by exact_mod_cast this
      rw [← key] at h'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hneg.ne

lemma sign_spec (z : CertField) :
    (0 < lowerHistorySign z → 0 < certFieldVal z) ∧
    (lowerHistorySign z < 0 → certFieldVal z < 0) ∧
    (lowerHistorySign z = 0 → certFieldVal z = 0) := by
  have hs7 := s7_pos
  have hc := conj_identity z
  rw [val_eq]
  set X : ℝ := (z.a:ℝ) + z.b * s3 with hX
  set Y : ℝ := (z.c:ℝ) + z.d * s3 with hY
  obtain ⟨x1, x2, x3⟩ := quadSign_spec z.a z.b
  obtain ⟨y1, y2, y3⟩ := quadSign_spec z.c z.d
  rw [← hX] at x1 x2 x3
  rw [← hY] at y1 y2 y3
  unfold lowerHistorySign
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  obtain ⟨w1, w2, w3⟩ := quadSign_spec u v
  dsimp only
  split_ifs with hx0 hy0 hxp hyp hyn
  · -- X = 0
    have hX0 := x3 hx0
    rw [hX0, zero_add]
    refine ⟨fun h => by have := y1 h; positivity, fun h => ?_, fun h => ?_⟩
    · have := y2 h; nlinarith
    · have := y3 h; rw [this]; ring
  · -- Y = 0
    have hY0 := y3 hy0
    rw [hY0, mul_zero, add_zero]
    exact ⟨x1, x2, x3⟩
  · -- X > 0, Y > 0
    have := x1 hxp
    have := y1 hyp
    refine ⟨fun _ => by positivity, fun h => by norm_num at h, fun h => by norm_num at h⟩
  · -- X > 0, Y < 0
    have hXp := x1 hxp
    have hYn : Y < 0 := y2 (lt_of_le_of_ne (not_lt.mp hyp) hy0)
    have hpos : 0 < X - s7 * Y := by nlinarith
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := w1 h; rw [← hc] at this; exact pos_of_mul_pos_left this hpos.le
    · have := w2 h; rw [← hc] at this; exact neg_of_mul_neg_left this hpos.le
    · have := w3 h; rw [← hc] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hpos.ne'
  · -- X < 0, Y < 0
    have hXn : X < 0 := x2 (lt_of_le_of_ne (not_lt.mp hxp) hx0)
    have hYn := y2 hyn
    refine ⟨fun h => by norm_num at h, fun _ => by nlinarith, fun h => by norm_num at h⟩
  · -- X < 0, Y > 0
    have hXn : X < 0 := x2 (lt_of_le_of_ne (not_lt.mp hxp) hx0)
    have hYp : 0 < Y := y1 (lt_of_le_of_ne (not_lt.mp hyn) (Ne.symm hy0))
    have hneg : X - s7 * Y < 0 := by nlinarith
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := w2 (by linarith); rw [← hc] at this; exact pos_of_mul_neg_left this hneg.le
    · have := w1 (by linarith); rw [← hc] at this; exact neg_of_mul_pos_left this hneg.le
    · have := w3 (by linarith); rw [← hc] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hneg.ne

lemma sign_nonneg_of (z : CertField) (h : 0 ≤ lowerHistorySign z) : 0 ≤ certFieldVal z := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt ((sign_spec z).1 h')
  · exact le_of_eq ((sign_spec z).2.2 h'.symm).symm
lemma sign_nonpos_of (z : CertField) (h : lowerHistorySign z ≤ 0) : certFieldVal z ≤ 0 := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt ((sign_spec z).2.1 h')
  · exact le_of_eq ((sign_spec z).2.2 h')

lemma abs_correct (z : CertField) : certFieldVal (lowerHistoryAbs z) = |certFieldVal z| := by
  unfold lowerHistoryAbs
  split_ifs with h
  · rw [val_neg, abs_of_neg ((sign_spec z).2.1 h)]
  · rw [abs_of_nonneg (sign_nonneg_of z (not_lt.mp h))]

/-! ### Möbius evaluation -/

lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

lemma pe_single (a : ℕ+) (x : ℝ) : prefixEval [a] x = 1 / (((a:ℕ):ℝ) + x) := rfl

lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

lemma pe_unit (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1/(((a:ℕ):ℝ)+prefixEval w x) ∧ 1/(((a:ℕ):ℝ)+prefixEval w x) ≤ 1
    have hpos : 0 < ((a:ℕ):ℝ)+prefixEval w x := by linarith [ih.1]
    constructor
    · exact le_of_lt (div_pos (by norm_num) hpos)
    · apply (div_le_iff₀ hpos).2
      linarith [ih.1]

def stepM (m : (ℕ × ℕ) × (ℕ × ℕ)) (a : ℕ+) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((m.1.2, m.1.1 + (a:ℕ) * m.1.2), (m.2.2, m.2.1 + (a:ℕ) * m.2.2))

lemma matrix_append (w : List ℕ+) (a : ℕ+) :
    lowerHistoryMatrix (w ++ [a]) = stepM (lowerHistoryMatrix w) a := by
  simp [lowerHistoryMatrix, List.foldl_append, stepM]

lemma matrix_nil : lowerHistoryMatrix [] = ((1,0),(0,1)) := rfl

lemma matrix_pos (w : List ℕ+) : 1 ≤ (lowerHistoryMatrix w).2.2 := by
  induction w using List.reverseRecOn with
  | nil => simp [matrix_nil]
  | append_singleton w a ih =>
    rw [matrix_append]
    simp only [stepM]
    have ha : 1 ≤ (a:ℕ) := a.pos
    nlinarith

lemma mobius (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    prefixEval w x =
      (((lowerHistoryMatrix w).1.1 : ℝ) * x + (lowerHistoryMatrix w).1.2) /
      (((lowerHistoryMatrix w).2.1 : ℝ) * x + (lowerHistoryMatrix w).2.2) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp [matrix_nil, prefixEval]
  | append_singleton w a ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hm := matrix_pos w
    have hm' : (1:ℝ) ≤ ((lowerHistoryMatrix w).2.2 : ℝ) := by exact_mod_cast hm
    have hden : 0 < ((lowerHistoryMatrix w).2.1 : ℝ) * (1 / (((a:ℕ):ℝ) + x)) + (lowerHistoryMatrix w).2.2 := by
      positivity
    rw [pe_append, pe_single, ih _ hx', matrix_append]
    simp only [stepM]
    push_cast
    field_simp
    ring

lemma cf_correct (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
  have hm := matrix_pos w
  have hm' : (1:ℝ) ≤ ((lowerHistoryMatrix w).2.2 : ℝ) := by exact_mod_cast hm
  have hden : ((lowerHistoryMatrix w).2.1 : ℝ) * certFieldVal z + (lowerHistoryMatrix w).2.2 ≠ 0 := by
    positivity
  unfold lowerHistoryCF
  rw [div_correct, val_add, val_add, val_scale, val_scale, val_rat, val_rat, mobius w _ hz]
  · push_cast; rfl
  · rw [val_add, val_scale, val_rat]; push_cast; exact hden

lemma val_alpha : certFieldVal lowerHistoryAlpha = lowerAlpha := by
  norm_num [certFieldVal, lowerHistoryAlpha, lowerAlpha]; ring
lemma val_beta : certFieldVal lowerHistoryBeta = lowerBeta := by
  norm_num [certFieldVal, lowerHistoryBeta, lowerBeta]; ring
lemma val_tau : certFieldVal lowerHistoryTau = lowerTau := by
  norm_num [certFieldVal, lowerHistoryTau, lowerTau]; ring

lemma ab_unit : lowerAlpha ∈ Set.Icc (0:ℝ) 1 ∧ lowerBeta ∈ Set.Icc (0:ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerAlpha, lowerBeta]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
lemma rho_unit : lowerTau ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 3 ≤ (2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerTau]
  exact ⟨by linarith, by linarith⟩

/-! ### Continuants and the signed difference identity -/

/-- real-valued continuants of `lowerCD`. -/
noncomputable def rCD (w : List ℕ+) : ℝ × ℝ := (((lowerCD w).1 : ℝ), ((lowerCD w).2 : ℝ))

lemma lowerCD_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

lemma cd_append (w : List ℕ+) (a : ℕ+) :
    rCD (w ++ [a]) = ((rCD w).2, (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2) := by
  simp only [rCD, lowerCD_append]; push_cast; rfl

lemma cd_nil : rCD [] = (0, 1) := by simp [rCD, lowerCD]

lemma ratio_eq (w : List ℕ+) : lowerRatio w = (rCD w).1 / (rCD w).2 := rfl

lemma cd_pos (w : List ℕ+) : 0 ≤ (rCD w).1 ∧ 0 < (rCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cd_nil]; norm_num
  | append_singleton w a ih =>
    rw [cd_append]
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    exact ⟨le_of_lt ih.2, by nlinarith [ih.1, ih.2]⟩

lemma param_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w :=
  div_nonneg (cd_pos w).1 (cd_pos w).2.le

/-- `(-1)^{|w|}` written with an `if`. -/
noncomputable def sgnOf (w : List ℕ+) : ℝ := if w.length % 2 = 0 then 1 else -1

lemma sgnOf_append (w : List ℕ+) (a : ℕ+) : sgnOf (w ++ [a]) = - sgnOf w := by
  unfold sgnOf
  have hl : (w ++ [a]).length = w.length + 1 := by simp
  rw [hl]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · rw [if_neg (by omega : ¬ (w.length + 1) % 2 = 0), if_pos h]; try norm_num
  · rw [if_pos (by omega : (w.length + 1) % 2 = 0), if_neg (by omega : ¬ w.length % 2 = 0)]; try norm_num

lemma sgnOf_sq (w : List ℕ+) : sgnOf w * sgnOf w = 1 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma pe_diff_raw (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) / (((rCD w).2 + (rCD w).1 * x) * ((rCD w).2 + (rCD w).1 * y)) := by
  induction w using List.reverseRecOn generalizing x y with
  | nil => simp [cd_nil, prefixEval, sgnOf]
  | append_singleton w a ih =>
    obtain ⟨hc, hd⟩ := cd_pos w
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hay : 0 < ((a:ℕ):ℝ) + y := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hy' : 0 ≤ 1 / (((a:ℕ):ℝ) + y) := by positivity
    have hdx : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + x)) := by positivity
    have hdy : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + y)) := by positivity
    have hdx' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * x := by positivity
    have hdy' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * y := by positivity
    rw [pe_append, pe_append, pe_single, pe_single, ih _ _ hx' hy', cd_append, sgnOf_append]
    simp only
    field_simp
    try ring

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) /
        ((rCD w).2 ^ 2 * (1 + lowerRatio w * x) * (1 + lowerRatio w * y)) := by
  rw [pe_diff_raw w x y hx hy]
  obtain ⟨hc, hd⟩ := cd_pos w
  congr 1
  rw [ratio_eq]
  field_simp
  try ring

lemma width_eq (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((rCD w).2 ^ 2 * (1 + lowerRatio w * lowerAlpha) * (1 + lowerRatio w * lowerBeta)) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  unfold lowerWidth
  rw [pe_diff w _ _ hb.1 ha.1]
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * lowerBeta) * (1 + lowerRatio w * lowerAlpha) := by
    have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
    have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
    positivity
  rw [abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul, abs_of_pos (sub_pos.mpr hab)]
  ring

lemma width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  rw [width_eq]
  have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
  have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
  apply div_pos (sub_pos.mpr hab)
  positivity

lemma width_append (w v : List ℕ+) : lowerWidth (w ++ v) =
    lowerWidth v / ((rCD w).2 ^ 2 *
      (1 + lowerRatio w * prefixEval v lowerAlpha) *
      (1 + lowerRatio w * prefixEval v lowerBeta)) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have ha := (pe_unit v lowerAlpha hA).1
  have hb := (pe_unit v lowerBeta hB).1
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * prefixEval v lowerBeta) *
      (1 + lowerRatio w * prefixEval v lowerAlpha) := by
    have : 0 ≤ lowerRatio w * prefixEval v lowerAlpha := mul_nonneg hp ha
    have : 0 ≤ lowerRatio w * prefixEval v lowerBeta := mul_nonneg hp hb
    positivity
  unfold lowerWidth
  rw [pe_append, pe_append, pe_diff w _ _ hb ha, abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul]
  ring

/-! ### Threshold values -/

lemma threshold_value (a x y : CertField) (u v : CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold a (x,y) (u,v)) r s =
      certFieldVal a * ((1+s*certFieldVal u)*(1+s*certFieldVal v)) /
        ((1+r*certFieldVal x)*(1+r*certFieldVal y)) := by
  unfold lowerHistoryThreshold lowerHistorySort
  split_ifs <;> simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

lemma scale_value (t : ℚ) (h : CertThreshold) (r s : ℝ) :
    certThresholdVal (lowerHistoryScaleThreshold t h) r s = (t:ℝ)*certThresholdVal h r s := by
  simp only [lowerHistoryScaleThreshold, certThresholdVal, certThresholdNum, certThresholdDen,
    certFieldScale, certFieldVal]
  push_cast
  ring

lemma complement_holds (b : CertBound) (p s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) p s q ↔ ¬ certBoundHolds b p s q := by
  rcases b with ⟨bl, bs, bt⟩
  cases bl <;> cases bs <;> simp [lowerHistoryComplement, certBoundHolds, not_le, not_lt]

lemma cf_alpha (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryAlpha) = prefixEval w lowerAlpha := by
  rw [cf_correct _ _ (by rw [val_alpha]; exact ab_unit.1.1), val_alpha]
lemma cf_beta (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryBeta) = prefixEval w lowerBeta := by
  rw [cf_correct _ _ (by rw [val_beta]; exact ab_unit.2.1.1), val_beta]
lemma cf_tau (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryTau) = prefixEval w lowerTau := by
  rw [cf_correct _ _ (by rw [val_tau]; exact rho_unit.1), val_tau]

lemma wh_value (w : LowerPair) (r s : ℝ) :
    certThresholdVal (lowerHistoryWH w) r s =
      (lowerWidth w.1 / lowerWidth w.2) *
        ((1+s*prefixEval w.2 lowerAlpha)*(1+s*prefixEval w.2 lowerBeta)) /
        ((1+r*prefixEval w.1 lowerAlpha)*(1+r*prefixEval w.1 lowerBeta)) := by
  have hne : certFieldVal (certFieldSub (lowerHistoryCF w.2 lowerHistoryAlpha)
      (lowerHistoryCF w.2 lowerHistoryBeta)) ≠ 0 := by
    rw [val_sub, cf_alpha, cf_beta]
    have := width_pos w.2
    unfold lowerWidth at this
    intro h
    rw [abs_sub_comm, h, abs_zero] at this
    exact lt_irrefl _ this
  unfold lowerHistoryWH
  rw [threshold_value, abs_correct, div_correct _ _ hne, val_sub, val_sub, abs_div]
  simp only [cf_alpha, cf_beta]
  unfold lowerWidth
  rw [abs_sub_comm (prefixEval w.1 lowerBeta), abs_sub_comm (prefixEval w.2 lowerBeta)]


/-! ### Endpoint-case development (m7struct4) -/

lemma append_singleton_suffix_iff (l x : List ℕ+) (c a : ℕ+) :
    l ++ [c] <:+ x ++ [a] ↔ c = a ∧ l <:+ x := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← List.append_assoc] at ht
    obtain ⟨h1, h2⟩ := List.append_inj' ht (by simp)
    simp only [List.cons.injEq, and_true] at h2
    exact ⟨h2, ⟨t, h1⟩⟩
  · rintro ⟨rfl, t, ht⟩
    exact ⟨t, by rw [← List.append_assoc, ht]⟩

lemma suffix3_transfer (b ctx ws : List ℕ+) (hs : sufCtx b ctx) :
    ([3] : List ℕ+) <:+ b ++ ws ↔ ([3] : List ℕ+) <:+ ctx ++ ws := by
  rcases ws with _ | ⟨a, _ | ⟨a', rest⟩⟩
  · simpa [lowerEnds] using hs.1
  · simp
  · constructor
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append b _) (by simp))
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append ctx _) (by simp))

lemma suffix31_transfer (b ctx ws : List ℕ+) (hs : sufCtx b ctx) :
    ([3,1] : List ℕ+) <:+ b ++ ws ↔ ([3,1] : List ℕ+) <:+ ctx ++ ws := by
  rcases ws with _ | ⟨a, _ | ⟨a', rest⟩⟩
  · simpa [lowerEnds] using hs.2
  · have e : ([3,1] : List ℕ+) = [3] ++ [1] := rfl
    rw [e, append_singleton_suffix_iff, append_singleton_suffix_iff]
    have := hs.1
    simp only [lowerEnds] at this
    rw [this]
  · constructor
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append b _) (by simp))
    · intro h
      exact List.suffix_append_of_suffix (List.suffix_of_suffix_length_le h (List.suffix_append ctx _) (by simp))

lemma odd_append (L M : List ℕ+) :
    decide ((L ++ M).length % 2 = 1) = xor (decide (L.length % 2 = 1)) (decide (M.length % 2 = 1)) := by
  rw [List.length_append]
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one M.length with h' | h' <;>
  simp [h, h', Nat.add_mod]

lemma even_eq (L : List ℕ+) : decide (L.length % 2 = 0) = !decide (L.length % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;> simp [h]

lemma prop_eq_bool (P : Prop) [Decidable P] (b : Bool) : (P = (b = true)) ↔ decide P = b := by
  cases b <;> simp [eq_iff_iff]

/-- per-side matching of the report's natural-shortening data with the history encoding. -/
lemma side_match (b ctx ws : List ℕ+) (hs : sufCtx b ctx) (par upper odd : Bool)
    (hodd : odd = xor (decide (b.length % 2 = 1)) par) :
    (decide ((b ++ ws).length % 2 = 0) = !(upper.xor odd) ↔
      xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true) ∧
    lowerNaturalShort (b ++ ws) (upper.xor odd) =
      decide ((if xor (!upper) (xor par (decide (ws.length % 2 = 1))) then [3,1] else [3] : List ℕ+) <:+ ctx ++ ws) ∧
    (∀ short : Bool, lowerEndpointSuffix (b ++ ws) (upper.xor odd) short =
      (if xor (!upper) (xor par (decide (ws.length % 2 = 1))) then (if short then [2,1,3] else [3])
        else (if short then [1,2,1,3] else [1,3]))) ∧
    (if ((b ++ ws).length % 2 = 0) = (!(upper.xor odd)) then ([3] : List ℕ+) else [1,3]) =
      (if xor (!upper) (xor par (decide (ws.length % 2 = 1))) then [3] else [1,3]) := by
  have hA : decide ((b ++ ws).length % 2 = 0) = !(upper.xor odd) ↔
      xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true := by
    rw [even_eq, odd_append, hodd]
    cases upper <;> cases par <;> cases decide (b.length % 2 = 1) <;> cases decide (ws.length % 2 = 1) <;> decide
  have hcond : (((b ++ ws).length % 2 = 0) = ((!(upper.xor odd)) = true)) ↔
      xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true := by
    rw [prop_eq_bool]; exact hA
  refine ⟨hA, ?_, ?_, ?_⟩
  · unfold lowerNaturalShort
    by_cases h : xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true
    · rw [if_pos (hcond.2 h), if_pos h]
      exact decide_eq_decide.mpr (suffix31_transfer b ctx ws hs)
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
      exact decide_eq_decide.mpr (suffix3_transfer b ctx ws hs)
  · intro short
    unfold lowerEndpointSuffix
    by_cases h : xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true
    · rw [if_pos (hcond.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
  · by_cases h : xor (!upper) (xor par (decide (ws.length % 2 = 1))) = true
    · rw [if_pos (hcond.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]

/-- shape of `lowerEqualWords` when the left side is (weakly) wider. -/
lemma equalWords_left (P : LowerPair) (u : Bool) (hW : lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEqualWords P u =
      (P.1 ++ lowerEndpointSuffix P.1 u (lowerNaturalShort P.1 u),
       P.2 ++ lowerEndpointSuffix P.2 u (lowerNaturalShort P.2 u ||
         (!lowerNaturalShort P.1 u && !lowerNaturalShort P.2 u &&
           decide (lowerWidth (P.1 ++ (if (P.1.length % 2 = 0) = (!u) then [3] else [1,3])) ≤
             (7/5 : ℝ) * lowerWidth (P.2 ++ (if (P.1.length % 2 = 0) = (!u) then [3] else [1,3])))))) := by
  unfold lowerEqualWords lowerNormalize
  simp only [hW, ↓reduceIte]

/-- shape of `lowerEqualWords` when the right side is strictly wider. -/
lemma equalWords_right (P : LowerPair) (u : Bool) (hW : ¬ lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEqualWords P u =
      (P.1 ++ lowerEndpointSuffix P.1 u (lowerNaturalShort P.1 u ||
         (!lowerNaturalShort P.2 u && !lowerNaturalShort P.1 u &&
           decide (lowerWidth (P.2 ++ (if (P.2.length % 2 = 0) = (!u) then [3] else [1,3])) ≤
             (7/5 : ℝ) * lowerWidth (P.1 ++ (if (P.2.length % 2 = 0) = (!u) then [3] else [1,3]))))),
       P.2 ++ lowerEndpointSuffix P.2 u (lowerNaturalShort P.2 u)) := by
  unfold lowerEqualWords lowerNormalize
  simp only [hW, ↓reduceIte]

/-- the virtual-upper test of the mixed case in history terms. -/
lemma virt_iff (b ws : List ℕ+) (par upper odd : Bool)
    (hodd : odd = xor (decide (b.length % 2 = 1)) par) :
    (upper.xor odd = decide ((b ++ ws).length % 2 = 0)) ↔
      upper = !(xor par (decide (ws.length % 2 = 1))) := by
  rw [even_eq, odd_append, hodd]
  cases upper <;> cases par <;> cases decide (b.length % 2 = 1) <;> cases decide (ws.length % 2 = 1) <;> decide

lemma mod_eq_of_decide (m n : ℕ) (h : decide (m % 2 = 1) = decide (n % 2 = 1)) : m % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [hm, hn] at h ⊢

lemma mod_ne_of_decide (m n : ℕ) (h : decide (m % 2 = 1) ≠ decide (n % 2 = 1)) : m % 2 ≠ n % 2 := by
  intro e; apply h; rw [e]

lemma ratio_pair (u v : List ℕ+) (w : LowerPair) :
    lowerWidth (u ++ w.1) / lowerWidth (v ++ w.2) =
      certThresholdVal (lowerHistoryWH w) (lowerRatio u) (lowerRatio v) /
        ((rCD u).2 ^ 2 / (rCD v).2 ^ 2) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hup := param_nonneg u
  have hvp := param_nonneg v
  have hud := (cd_pos u).2
  have hvd := (cd_pos v).2
  have ha1 := (pe_unit w.1 lowerAlpha hA).1
  have hb1 := (pe_unit w.1 lowerBeta hB).1
  have ha2 := (pe_unit w.2 lowerAlpha hA).1
  have hb2 := (pe_unit w.2 lowerBeta hB).1
  have hw1 := width_pos w.1
  have hw2 := width_pos w.2
  have h1 : 0 < 1 + lowerRatio u * prefixEval w.1 lowerAlpha := by positivity
  have h2 : 0 < 1 + lowerRatio u * prefixEval w.1 lowerBeta := by positivity
  have h3 : 0 < 1 + lowerRatio v * prefixEval w.2 lowerAlpha := by positivity
  have h4 : 0 < 1 + lowerRatio v * prefixEval w.2 lowerBeta := by positivity
  rw [width_append, width_append, wh_value w]
  field_simp
  try ring

/-- the exact value of the normalization threshold at the base parameters. -/
lemma wh_key (base words : LowerPair) :
    certThresholdVal (lowerHistoryWH words) (lowerRatio base.1) (lowerRatio base.2) =
      lowerScale base * (lowerWidth (base.1++words.1) / lowerWidth (base.2++words.2)) := by
  have hr : lowerWidth (base.1 ++ words.1) / lowerWidth (base.2 ++ words.2) =
      certThresholdVal (lowerHistoryWH words) (lowerRatio base.1) (lowerRatio base.2) /
        ((rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2) := ratio_pair base.1 base.2 words
  have hs : lowerScale base = (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2 := rfl
  rw [hr, hs]
  have := (cd_pos base.1).2; have := (cd_pos base.2).2
  field_simp

/-- the scaled auxiliary cut of the equal case: `(5/7)·aux ≤ q ↔ W₁ ≤ (7/5) W₂`. -/
lemma cut_lower_iff (base : LowerPair) (v : LowerPair) :
    certBoundHolds ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH v)⟩
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerWidth (base.1 ++ v.1) ≤ (7/5 : ℝ) * lowerWidth (base.2 ++ v.2) := by
  simp only [certBoundHolds, Bool.false_eq_true, ↓reduceIte, scale_value, wh_key]
  have hq : 0 < lowerScale base := by
    show 0 < (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2
    have := (cd_pos base.1).2; have := (cd_pos base.2).2; positivity
  have h2 := width_pos (base.2 ++ v.2)
  push_cast
  rw [show ((5:ℝ)/7) * (lowerScale base * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) =
      lowerScale base * ((5/7) * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) by ring,
    mul_le_iff_le_one_right hq, ← mul_div_assoc, div_le_one h2]
  constructor <;> intro h <;> linarith

/-- the scaled auxiliary cut of the swapped equal case: `q ≤ (7/5)·aux ↔ W₂ ≤ (7/5) W₁`. -/
lemma cut_upper_iff (base : LowerPair) (v : LowerPair) :
    certBoundHolds ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH v)⟩
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerWidth (base.2 ++ v.2) ≤ (7/5 : ℝ) * lowerWidth (base.1 ++ v.1) := by
  simp only [certBoundHolds, Bool.false_eq_true, ↓reduceIte, scale_value, wh_key]
  have hq : 0 < lowerScale base := by
    show 0 < (rCD base.1).2 ^ 2 / (rCD base.2).2 ^ 2
    have := (cd_pos base.1).2; have := (cd_pos base.2).2; positivity
  have h2 := width_pos (base.2 ++ v.2)
  push_cast
  rw [show ((7:ℝ)/5) * (lowerScale base * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) =
      lowerScale base * ((7/5) * (lowerWidth (base.1 ++ v.1) / lowerWidth (base.2 ++ v.2))) by ring,
    le_mul_iff_one_le_right hq, ← mul_div_assoc, one_le_div h2]

lemma scale_eq (p : LowerPair) : lowerScale p = (rCD p.1).2 ^ 2 / (rCD p.2).2 ^ 2 := rfl

end LowerDev


namespace S14Tie

lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

lemma pe_single (a : ℕ+) (x : ℝ) : prefixEval [a] x = 1 / (((a:ℕ):ℝ) + x) := rfl

lemma ab_unit : lowerAlpha ∈ Set.Icc (0:ℝ) 1 ∧ lowerBeta ∈ Set.Icc (0:ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerAlpha, lowerBeta]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
lemma rho_unit : lowerTau ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 3 ≤ (2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [lowerTau]
  exact ⟨by linarith, by linarith⟩

/-! ### Continuants and the signed difference identity -/

/-- real-valued continuants of `lowerCD`. -/
noncomputable def rCD (w : List ℕ+) : ℝ × ℝ := (((lowerCD w).1 : ℝ), ((lowerCD w).2 : ℝ))

lemma lowerCD_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
  simp [lowerCD, List.foldl_append]

lemma cd_append (w : List ℕ+) (a : ℕ+) :
    rCD (w ++ [a]) = ((rCD w).2, (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2) := by
  simp only [rCD, lowerCD_append]; push_cast; rfl

lemma cd_nil : rCD [] = (0, 1) := by simp [rCD, lowerCD]

lemma ratio_eq (w : List ℕ+) : lowerRatio w = (rCD w).1 / (rCD w).2 := rfl

lemma cd_pos (w : List ℕ+) : 0 ≤ (rCD w).1 ∧ 0 < (rCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cd_nil]; norm_num
  | append_singleton w a ih =>
    rw [cd_append]
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    exact ⟨le_of_lt ih.2, by nlinarith [ih.1, ih.2]⟩

lemma param_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w :=
  div_nonneg (cd_pos w).1 (cd_pos w).2.le

/-- `(-1)^{|w|}` written with an `if`. -/
noncomputable def sgnOf (w : List ℕ+) : ℝ := if w.length % 2 = 0 then 1 else -1

lemma sgnOf_append (w : List ℕ+) (a : ℕ+) : sgnOf (w ++ [a]) = - sgnOf w := by
  unfold sgnOf
  have hl : (w ++ [a]).length = w.length + 1 := by simp
  rw [hl]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · rw [if_neg (by omega : ¬ (w.length + 1) % 2 = 0), if_pos h]; try norm_num
  · rw [if_pos (by omega : (w.length + 1) % 2 = 0), if_neg (by omega : ¬ w.length % 2 = 0)]; try norm_num

lemma sgnOf_sq (w : List ℕ+) : sgnOf w * sgnOf w = 1 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma pe_diff_raw (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) / (((rCD w).2 + (rCD w).1 * x) * ((rCD w).2 + (rCD w).1 * y)) := by
  induction w using List.reverseRecOn generalizing x y with
  | nil => simp [cd_nil, prefixEval, sgnOf]
  | append_singleton w a ih =>
    obtain ⟨hc, hd⟩ := cd_pos w
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hay : 0 < ((a:ℕ):ℝ) + y := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hy' : 0 ≤ 1 / (((a:ℕ):ℝ) + y) := by positivity
    have hdx : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + x)) := by positivity
    have hdy : 0 < (rCD w).2 + (rCD w).1 * (1 / (((a:ℕ):ℝ) + y)) := by positivity
    have hdx' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * x := by positivity
    have hdy' : 0 < (rCD w).1 + ((a:ℕ):ℝ) * (rCD w).2 + (rCD w).2 * y := by positivity
    rw [pe_append, pe_append, pe_single, pe_single, ih _ _ hx' hy', cd_append, sgnOf_append]
    simp only
    field_simp
    try ring

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) /
        ((rCD w).2 ^ 2 * (1 + lowerRatio w * x) * (1 + lowerRatio w * y)) := by
  rw [pe_diff_raw w x y hx hy]
  obtain ⟨hc, hd⟩ := cd_pos w
  congr 1
  rw [ratio_eq]
  field_simp
  try ring

lemma width_eq (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((rCD w).2 ^ 2 * (1 + lowerRatio w * lowerAlpha) * (1 + lowerRatio w * lowerBeta)) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  unfold lowerWidth
  rw [pe_diff w _ _ hb.1 ha.1]
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * lowerBeta) * (1 + lowerRatio w * lowerAlpha) := by
    have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
    have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
    positivity
  rw [abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul, abs_of_pos (sub_pos.mpr hab)]
  ring

lemma width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  rw [width_eq]
  have : 0 ≤ lowerRatio w * lowerAlpha := mul_nonneg hp ha.1
  have : 0 ≤ lowerRatio w * lowerBeta := mul_nonneg hp hb.1
  apply div_pos (sub_pos.mpr hab)
  positivity

lemma rCD_fst (w : List ℕ+) : (rCD w).1 = ((lowerCD w).1 : ℝ) := rfl
lemma rCD_snd (w : List ℕ+) : (rCD w).2 = ((lowerCD w).2 : ℝ) := rfl

/-! ### The integer normal form of a width -/

def wA (w : List ℕ+) : ℤ := ((lowerCD w).1 : ℤ)^2 + ((lowerCD w).2 : ℤ)^2
def wB (w : List ℕ+) : ℤ :=
  4*((lowerCD w).1 : ℤ)*((lowerCD w).2 : ℤ) - 3*((lowerCD w).1 : ℤ)^2

lemma wA_cast (w : List ℕ+) : ((wA w : ℤ) : ℝ) = (rCD w).1^2 + (rCD w).2^2 := by
  rw [rCD_fst, rCD_snd]; simp only [wA]; push_cast; ring
lemma wB_cast (w : List ℕ+) :
    ((wB w : ℤ) : ℝ) = 4*(rCD w).1*(rCD w).2 - 3*(rCD w).1^2 := by
  rw [rCD_fst, rCD_snd]; simp only [wB]; push_cast; ring

lemma beta_eq : lowerBeta = 3 * lowerAlpha := by
  simp only [lowerAlpha, lowerBeta]; ring

lemma alpha_sq : 3 * lowerAlpha^2 = 1 - 3*lowerAlpha := by
  have h : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  simp only [lowerAlpha]
  nlinarith [h]

lemma width_AB (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) / ((wA w : ℝ) + lowerAlpha * (wB w : ℝ)) := by
  rw [width_eq]
  congr 1
  have hd : (rCD w).2 ≠ 0 := ne_of_gt (cd_pos w).2
  have key : (rCD w).2 ^ 2 * (1 + lowerRatio w * lowerAlpha) * (1 + lowerRatio w * lowerBeta)
      = ((rCD w).2 + (rCD w).1 * lowerAlpha) * ((rCD w).2 + (rCD w).1 * lowerBeta) := by
    rw [ratio_eq]; field_simp
  rw [key, wA_cast, wB_cast, beta_eq]
  linear_combination ((rCD w).1^2) * alpha_sq

lemma width_den_pos (w : List ℕ+) : 0 < (wA w : ℝ) + lowerAlpha * (wB w : ℝ) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hnum : (0:ℝ) < lowerBeta - lowerAlpha := sub_pos.mpr hab
  have h2 := width_pos w
  rw [width_AB w] at h2
  rcases lt_trichotomy ((wA w : ℝ) + lowerAlpha * (wB w : ℝ)) 0 with hc | hc | hc
  · have : (lowerBeta - lowerAlpha) / ((wA w : ℝ) + lowerAlpha * (wB w : ℝ)) < 0 :=
      div_neg_of_pos_of_neg hnum hc
    linarith
  · rw [hc, div_zero] at h2; linarith
  · exact hc

/-! ### Irrationality: a width determines the integer pair `(wA, wB)` -/

lemma not_isSquare_of (n : ℕ) (h : ∀ r ≤ n, r * r ≠ n) : ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hle : r ≤ n := by nlinarith
  exact h r hle hr.symm

lemma irr21 : Irrational (Real.sqrt 21) := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_of 21 (by decide))
  simpa using this

lemma lin_indep (x y : ℤ) (h : (x : ℝ) + lowerAlpha * (y : ℝ) = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hy' : ((y : ℝ)) ≠ 0 := by exact_mod_cast hy
    apply irr21
    refine ⟨(-6*x/y : ℚ) + 3, ?_⟩
    have hA : lowerAlpha = -(x : ℝ)/(y : ℝ) := by
      field_simp
      linarith
    have h21 : Real.sqrt 21 = 6 * lowerAlpha + 3 := by
      simp only [lowerAlpha]; ring
    rw [h21, hA]
    push_cast
    field_simp

lemma tie_AB (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) : wA u = wA v ∧ wB u = wB v := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hnum : (0:ℝ) < lowerBeta - lowerAlpha := sub_pos.mpr hab
  have hu := width_den_pos u
  have hv := width_den_pos v
  rw [width_AB u, width_AB v, div_eq_div_iff (ne_of_gt hu) (ne_of_gt hv)] at h
  have h2 : (lowerBeta - lowerAlpha) *
      (((wA v : ℝ) + lowerAlpha * (wB v : ℝ)) - ((wA u : ℝ) + lowerAlpha * (wB u : ℝ))) = 0 := by
    linarith
  have hden : (wA u : ℝ) + lowerAlpha * (wB u : ℝ) = (wA v : ℝ) + lowerAlpha * (wB v : ℝ) := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso; linarith
    · linarith
  have := lin_indep (wA u - wA v) (wB u - wB v) (by push_cast; linarith)
  exact ⟨by omega, by omega⟩

/-! ### Elementary continuant facts -/

lemma cd_den_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  have h := (cd_pos w).2
  rw [rCD_snd] at h
  exact_mod_cast h

lemma cd_num_pos (w : List ℕ+) (h : w ≠ []) : 0 < (lowerCD w).1 := by
  induction w using List.reverseRecOn with
  | nil => exact absurd rfl h
  | append_singleton w a _ => rw [lowerCD_append]; exact cd_den_pos w

lemma cd_le (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => simp [lowerCD]
  | append_singleton w a _ =>
    rw [lowerCD_append]
    have hmul : (lowerCD w).2 ≤ (a:ℕ) * (lowerCD w).2 := Nat.le_mul_of_pos_left _ a.pos
    omega

lemma cd_lt (w : List ℕ+) (h : w ≠ [1]) : (lowerCD w).1 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => simp [lowerCD]
  | append_singleton w a _ =>
    rw [lowerCD_append]
    have hd := cd_den_pos w
    have hmul : (lowerCD w).2 ≤ (a:ℕ) * (lowerCD w).2 := Nat.le_mul_of_pos_left _ a.pos
    rcases eq_or_ne w ([] : List ℕ+) with hw | hw
    · subst hw
      have h1 : (a:ℕ) ≠ 1 := by
        intro hc
        apply h
        have hone : a = 1 := PNat.coe_eq_one_iff.mp hc
        simp [hone]
      have h2 : 1 ≤ (a:ℕ) := a.pos
      show (1:ℕ) < 0 + (a:ℕ) * 1
      omega
    · have := cd_num_pos w hw
      omega

/-! ### The tie dichotomy -/

lemma tie_dichotomy (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) :
    lowerCD u = lowerCD v ∨
      4*((lowerCD u).2 : ℤ)*((lowerCD v).2 : ℤ) =
        3*(((lowerCD u).1 : ℤ)*((lowerCD v).2 : ℤ) + ((lowerCD v).1 : ℤ)*((lowerCD u).2 : ℤ))
          + 4*((lowerCD u).1 : ℤ)*((lowerCD v).1 : ℤ) := by
  obtain ⟨hA, hB⟩ := tie_AB u v h
  have hA' : ((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2
      = ((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2 := by simpa [wA] using hA
  have hB' : 4*((lowerCD u).1:ℤ)*((lowerCD u).2:ℤ) - 3*((lowerCD u).1:ℤ)^2
      = 4*((lowerCD v).1:ℤ)*((lowerCD v).2:ℤ) - 3*((lowerCD v).1:ℤ)^2 := by simpa [wB] using hB
  have hDu : (0:ℤ) < ((lowerCD u).2:ℤ) := by exact_mod_cast cd_den_pos u
  have hDv : (0:ℤ) < ((lowerCD v).2:ℤ) := by exact_mod_cast cd_den_pos v
  have key : (((lowerCD u).1:ℤ)*((lowerCD v).2:ℤ) - ((lowerCD v).1:ℤ)*((lowerCD u).2:ℤ)) *
      (4*((lowerCD u).2:ℤ)*((lowerCD v).2:ℤ)
        - 3*(((lowerCD u).1:ℤ)*((lowerCD v).2:ℤ) + ((lowerCD v).1:ℤ)*((lowerCD u).2:ℤ))
        - 4*((lowerCD u).1:ℤ)*((lowerCD v).1:ℤ)) = 0 := by
    linear_combination (-(4*((lowerCD v).1:ℤ)*((lowerCD v).2:ℤ) - 3*((lowerCD v).1:ℤ)^2)) * hA'
      + (((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2) * hB'
  rcases mul_eq_zero.mp key with hk | hk
  · left
    have hCD : ((lowerCD u).1:ℤ)*((lowerCD v).2:ℤ) = ((lowerCD v).1:ℤ)*((lowerCD u).2:ℤ) := by
      linarith
    have hApos : (0:ℤ) < ((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2 := by nlinarith
    have hsq : ((lowerCD u).2:ℤ)^2 * (((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2)
        = ((lowerCD v).2:ℤ)^2 * (((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2) := by
      linear_combination (-(((lowerCD u).2:ℤ)*((lowerCD v).1:ℤ)
        + ((lowerCD u).1:ℤ)*((lowerCD v).2:ℤ))) * hCD
    have hDeq : ((lowerCD u).2:ℤ)^2 = ((lowerCD v).2:ℤ)^2 := by
      rw [← hA'] at hsq
      exact mul_right_cancel₀ (ne_of_gt hApos) hsq
    have hDuv : ((lowerCD u).2:ℤ) = ((lowerCD v).2:ℤ) := by nlinarith
    have hCuv : ((lowerCD u).1:ℤ) = ((lowerCD v).1:ℤ) := by
      have hx : ((lowerCD u).1:ℤ)*((lowerCD v).2:ℤ) = ((lowerCD v).1:ℤ)*((lowerCD v).2:ℤ) := by
        rw [hCD, hDuv]
      exact mul_right_cancel₀ (ne_of_gt hDv) hx
    have h1 : (lowerCD u).1 = (lowerCD v).1 := by exact_mod_cast hCuv
    have h2 : (lowerCD u).2 = (lowerCD v).2 := by exact_mod_cast hDuv
    exact Prod.ext h1 h2
  · right; linarith

/-- at a width tie, the side whose ratio exceeds `1/2` has the larger numerator continuant -/
lemma cd_le_of_tie (u v : List ℕ+) (h : lowerWidth u = lowerWidth v)
    (hv : (lowerCD v).2 < 2*(lowerCD v).1) : (lowerCD u).1 ≤ (lowerCD v).1 := by
  obtain ⟨hA, hB⟩ := tie_AB u v h
  have hA' : ((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2
      = ((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2 := by simpa [wA] using hA
  have hDu : (0:ℤ) < ((lowerCD u).2:ℤ) := by exact_mod_cast cd_den_pos u
  have hDv : (0:ℤ) < ((lowerCD v).2:ℤ) := by exact_mod_cast cd_den_pos v
  have hCu0 : (0:ℤ) ≤ ((lowerCD u).1:ℤ) := by positivity
  have hCv0 : (0:ℤ) ≤ ((lowerCD v).1:ℤ) := by positivity
  have hCuDu : ((lowerCD u).1:ℤ) ≤ ((lowerCD u).2:ℤ) := by exact_mod_cast cd_le u
  have hvZ : ((lowerCD v).2:ℤ) < 2*((lowerCD v).1:ℤ) := by exact_mod_cast hv
  rcases tie_dichotomy u v h with hcd | href
  · rw [hcd]
  · by_contra hcon
    push_neg at hcon
    have hlt : ((lowerCD v).1:ℤ) < ((lowerCD u).1:ℤ) := by exact_mod_cast hcon
    have hCu1 : (1:ℤ) ≤ ((lowerCD u).1:ℤ) := by linarith
    have hpos : (0:ℤ) < 4*((lowerCD u).2:ℤ) - 3*((lowerCD u).1:ℤ) := by linarith
    have hCv1 : (1:ℤ) ≤ ((lowerCD v).1:ℤ) := by
      by_contra hc
      push_neg at hc
      have hz : ((lowerCD v).1:ℤ) = 0 := le_antisymm (by linarith) hCv0
      rw [hz] at href
      nlinarith
    have hkey : 2*((lowerCD u).1:ℤ) < ((lowerCD u).2:ℤ) := by nlinarith
    nlinarith

/-! ### Appending `[3]` -/

lemma cd_append3 (w : List ℕ+) :
    lowerCD (w ++ [3]) = ((lowerCD w).2, (lowerCD w).1 + 3*(lowerCD w).2) := by
  rw [lowerCD_append]; norm_num

lemma width_append3_le (u v : List ℕ+) (h : lowerWidth u = lowerWidth v)
    (hc : (lowerCD u).1 ≤ (lowerCD v).1) :
    lowerWidth (u ++ [3]) ≤ lowerWidth (v ++ [3]) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  obtain ⟨hA, hB⟩ := tie_AB u v h
  have hA' : ((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2
      = ((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2 := by simpa [wA] using hA
  have hB' : 4*((lowerCD u).1:ℤ)*((lowerCD u).2:ℤ) - 3*((lowerCD u).1:ℤ)^2
      = 4*((lowerCD v).1:ℤ)*((lowerCD v).2:ℤ) - 3*((lowerCD v).1:ℤ)^2 := by simpa [wB] using hB
  have hcz : ((lowerCD u).1:ℤ) ≤ ((lowerCD v).1:ℤ) := by exact_mod_cast hc
  have hCu0 : (0:ℤ) ≤ ((lowerCD u).1:ℤ) := by positivity
  have hAu : wA (u ++ [3]) = ((lowerCD u).2:ℤ)^2 + (((lowerCD u).1:ℤ) + 3*((lowerCD u).2:ℤ))^2 := by
    simp only [wA, cd_append3]; push_cast; ring
  have hAv : wA (v ++ [3]) = ((lowerCD v).2:ℤ)^2 + (((lowerCD v).1:ℤ) + 3*((lowerCD v).2:ℤ))^2 := by
    simp only [wA, cd_append3]; push_cast; ring
  have hBu : wB (u ++ [3]) = 4*((lowerCD u).2:ℤ)*(((lowerCD u).1:ℤ) + 3*((lowerCD u).2:ℤ))
      - 3*((lowerCD u).2:ℤ)^2 := by simp only [wB, cd_append3]; push_cast; ring
  have hBv : wB (v ++ [3]) = 4*((lowerCD v).2:ℤ)*(((lowerCD v).1:ℤ) + 3*((lowerCD v).2:ℤ))
      - 3*((lowerCD v).2:ℤ)^2 := by simp only [wB, cd_append3]; push_cast; ring
  have hdA : 2*(wA (u ++ [3]) - wA (v ++ [3]))
      = -9*(((lowerCD u).1:ℤ)^2 - ((lowerCD v).1:ℤ)^2) := by
    rw [hAu, hAv]; linear_combination 20*hA' + 3*hB'
  have hdB : wB (u ++ [3]) - wB (v ++ [3])
      = -6*(((lowerCD u).1:ℤ)^2 - ((lowerCD v).1:ℤ)^2) := by
    rw [hBu, hBv]; linear_combination 9*hA' + hB'
  have hsq : (((lowerCD u).1:ℤ)^2 - ((lowerCD v).1:ℤ)^2) ≤ 0 := by nlinarith
  have h1 : ((2*(wA (u ++ [3]) - wA (v ++ [3])) : ℤ) : ℝ)
      = ((-9*(((lowerCD u).1:ℤ)^2 - ((lowerCD v).1:ℤ)^2) : ℤ) : ℝ) := by exact_mod_cast hdA
  have h2 : ((wB (u ++ [3]) - wB (v ++ [3]) : ℤ) : ℝ)
      = ((-6*(((lowerCD u).1:ℤ)^2 - ((lowerCD v).1:ℤ)^2) : ℤ) : ℝ) := by exact_mod_cast hdB
  have h3 : ((((lowerCD u).1:ℤ)^2 - ((lowerCD v).1:ℤ)^2 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hsq
  push_cast at h1 h2 h3
  have hden : (wA (v ++ [3]) : ℝ) + lowerAlpha * (wB (v ++ [3]) : ℝ)
      ≤ (wA (u ++ [3]) : ℝ) + lowerAlpha * (wB (u ++ [3]) : ℝ) := by nlinarith [ha.1]
  rw [width_AB (u ++ [3]), width_AB (v ++ [3])]
  exact div_le_div_of_nonneg_left (by linarith) (width_den_pos (v ++ [3])) hden

/-! ### The two endpoint-suffix values and the sign constant `K` -/

noncomputable def pL : ℝ := prefixEval [3] lowerTau
noncomputable def pS : ℝ := prefixEval [2,1,3] lowerTau

lemma sqrt3_bounds : (17/10 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (18/10 : ℝ) := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hnn := Real.sqrt_nonneg 3
  constructor <;> nlinarith [h3, hnn]

lemma pL_eq : pL = 2 - Real.sqrt 3 := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  have hs : pL = 1 / (3 + (Real.sqrt 3 - 1)) := by
    simp only [pL, prefixEval, lowerTau]; norm_num
  rw [hs]
  have n1 : (3:ℝ) + (Real.sqrt 3 - 1) ≠ 0 := by nlinarith
  rw [div_eq_iff n1]; nlinarith

lemma pS_eq : pS = (15 - Real.sqrt 3)/37 := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  have hs : pS = 1 / (2 + 1 / (1 + 1 / (3 + (Real.sqrt 3 - 1)))) := by
    simp only [pS, prefixEval, lowerTau]; norm_num
  rw [hs]
  have d1 : (3:ℝ) + (Real.sqrt 3 - 1) = 2 + Real.sqrt 3 := by ring
  rw [d1]
  have n1 : (2:ℝ) + Real.sqrt 3 ≠ 0 := by nlinarith
  have e1 : (1:ℝ) / (2 + Real.sqrt 3) = 2 - Real.sqrt 3 := by
    rw [div_eq_iff n1]; nlinarith
  rw [e1]
  have e2 : (1:ℝ) + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 := by ring
  rw [e2]
  have n2 : (3:ℝ) - Real.sqrt 3 ≠ 0 := by nlinarith
  have e3 : (1:ℝ) / (3 - Real.sqrt 3) = (3 + Real.sqrt 3)/6 := by
    rw [div_eq_div_iff n2 (by norm_num)]; nlinarith
  rw [e3]
  have e4 : (2:ℝ) + (3 + Real.sqrt 3)/6 = (15 + Real.sqrt 3)/6 := by ring
  rw [e4, one_div_div]
  have n3 : (15:ℝ) + Real.sqrt 3 ≠ 0 := by nlinarith
  rw [div_eq_div_iff n3 (by norm_num)]; nlinarith

lemma pL_lt_pS : pL < pS := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  rw [pL_eq, pS_eq]; nlinarith

lemma pL_nonneg : 0 ≤ pL := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds; rw [pL_eq]; nlinarith
lemma pS_nonneg : 0 ≤ pS := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds; rw [pS_eq]; nlinarith

/-- the sign constant of the reflection branch -/
lemma K_neg : pL*pS + (3/4)*(pL+pS) - 1 < 0 := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  rw [pL_eq, pS_eq]; nlinarith

/-- the `pe_diff` denominator at the pair `(pL, pS)` -/
noncomputable def Gval (w : List ℕ+) : ℝ :=
  (rCD w).2 ^ 2 * (1 + lowerRatio w * pL) * (1 + lowerRatio w * pS)

lemma Gval_eq (w : List ℕ+) :
    Gval w = ((rCD w).2 + (rCD w).1 * pL) * ((rCD w).2 + (rCD w).1 * pS) := by
  have hd : (rCD w).2 ≠ 0 := ne_of_gt (cd_pos w).2
  unfold Gval
  rw [ratio_eq]
  field_simp

lemma Gval_pos (w : List ℕ+) : 0 < Gval w := by
  rw [Gval_eq]
  have hd := (cd_pos w).2
  have hc := (cd_pos w).1
  have hl := pL_nonneg
  have hss := pS_nonneg
  have h1 : 0 < (rCD w).2 + (rCD w).1 * pL := by nlinarith
  have h2 : 0 < (rCD w).2 + (rCD w).1 * pS := by nlinarith
  exact mul_pos h1 h2

/-- at a width tie the side with the smaller numerator continuant has the larger `Gval` -/
lemma Gval_ge_of_tie (u v : List ℕ+) (h : lowerWidth u = lowerWidth v)
    (hc : (lowerCD u).1 ≤ (lowerCD v).1) : Gval v ≤ Gval u := by
  obtain ⟨hA, hB⟩ := tie_AB u v h
  have hA' : ((lowerCD u).1:ℤ)^2 + ((lowerCD u).2:ℤ)^2
      = ((lowerCD v).1:ℤ)^2 + ((lowerCD v).2:ℤ)^2 := by simpa [wA] using hA
  have hB' : 4*((lowerCD u).1:ℤ)*((lowerCD u).2:ℤ) - 3*((lowerCD u).1:ℤ)^2
      = 4*((lowerCD v).1:ℤ)*((lowerCD v).2:ℤ) - 3*((lowerCD v).1:ℤ)^2 := by simpa [wB] using hB
  have hAR : (rCD u).1^2 + (rCD u).2^2 = (rCD v).1^2 + (rCD v).2^2 := by
    rw [rCD_fst, rCD_snd, rCD_fst, rCD_snd]; exact_mod_cast hA'
  have hBR : 4*(rCD u).1*(rCD u).2 - 3*(rCD u).1^2
      = 4*(rCD v).1*(rCD v).2 - 3*(rCD v).1^2 := by
    rw [rCD_fst, rCD_snd, rCD_fst, rCD_snd]; exact_mod_cast hB'
  have hcR : (rCD u).1 ≤ (rCD v).1 := by
    rw [rCD_fst, rCD_fst]; exact_mod_cast hc
  have hu0 := (cd_pos u).1
  have hKey : Gval u - Gval v =
      ((rCD u).1^2 - (rCD v).1^2) * (pL*pS + (3/4)*(pL+pS) - 1) := by
    rw [Gval_eq, Gval_eq]
    linear_combination hAR + ((pL+pS)/4) * hBR
  have hsq : (rCD u).1^2 - (rCD v).1^2 ≤ 0 := by nlinarith
  nlinarith [hKey, hsq, K_neg]

/-! ### The signed endpoint comparison at a tie -/

lemma sgnOf_cases (w : List ℕ+) : sgnOf w = 1 ∨ sgnOf w = -1 := by
  unfold sgnOf; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma sign_helper (sg c G1 G2 : ℝ) (hs : sg = 1 ∨ sg = -1) (hc : c < 0)
    (hG1 : 0 < G1) (hG2 : 0 < G2) (hle : G2 ≤ G1) :
    0 ≤ sg * (sg * c / G1 - sg * c / G2) := by
  have hinv : 1/G1 ≤ 1/G2 := one_div_le_one_div_of_le hG2 hle
  have hd1 : ∀ x : ℝ, x / G1 = x * (1/G1) := fun x => by rw [div_eq_mul_one_div]
  have hd2 : ∀ x : ℝ, x / G2 = x * (1/G2) := fun x => by rw [div_eq_mul_one_div]
  rw [hd1, hd2]
  rcases hs with h | h <;> subst h <;> nlinarith [hinv, hc]

lemma sign_helper2 (sg c G : ℝ) (hs : sg = 1 ∨ sg = -1) (hc : c < 0) (hG : 0 < G) :
    0 ≤ sg * -(sg * c / G) := by
  have hp : 0 < 1/G := one_div_pos.mpr hG
  rcases hs with h | h <;> subst h <;> rw [div_eq_mul_one_div] <;> nlinarith [hp, hc]



lemma equalWords_left (P : LowerPair) (u : Bool) (hW : lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEqualWords P u =
      (P.1 ++ lowerEndpointSuffix P.1 u (lowerNaturalShort P.1 u),
       P.2 ++ lowerEndpointSuffix P.2 u (lowerNaturalShort P.2 u ||
         (!lowerNaturalShort P.1 u && !lowerNaturalShort P.2 u &&
           decide (lowerWidth (P.1 ++ (if (P.1.length % 2 = 0) = (!u) then [3] else [1,3])) ≤
             (7/5 : ℝ) * lowerWidth (P.2 ++ (if (P.1.length % 2 = 0) = (!u) then [3] else [1,3])))))) := by
  unfold lowerEqualWords lowerNormalize
  simp only [hW, ↓reduceIte]

lemma pe_L (w : List ℕ+) : prefixEval (w ++ [3]) lowerTau = prefixEval w pL := by
  rw [pe_append]; rfl
lemma pe_S (w : List ℕ+) : prefixEval (w ++ [2,1,3]) lowerTau = prefixEval w pS := by
  rw [pe_append]; rfl

lemma pe_LS (w : List ℕ+) :
    prefixEval w pL - prefixEval w pS = sgnOf w * (pL - pS) / Gval w := by
  rw [pe_diff w pL pS pL_nonneg pS_nonneg]; rfl

/-- at an exact width tie the two orders of an equal-parity pair give endpoints whose
difference has the sign of `(-1)^{|x₁|}`. -/
lemma endpoint_tie_sign (x1 x2 : List ℕ+) (u : Bool)
    (hpar : x1.length % 2 = x2.length % 2)
    (hfam : ((x1.length % 2 = 0) = ((!u) = true)))
    (htie : lowerWidth x1 = lowerWidth x2)
    (hcd : (lowerCD x1).1 ≤ (lowerCD x2).1) :
    0 ≤ sgnOf x1 * (lowerEndpoint (x1,x2) u - lowerEndpoint (x2,x1) u) := by
  classical
  have hfam2 : ((x2.length % 2 = 0) = ((!u) = true)) := by rw [← hpar]; exact hfam
  have hle1 : lowerWidth (x1,x2).2 ≤ lowerWidth (x1,x2).1 := le_of_eq htie.symm
  have hle2 : lowerWidth (x2,x1).2 ≤ lowerWidth (x2,x1).1 := le_of_eq htie
  have hEW1 : lowerEndpointWords (x1,x2) u = lowerEqualWords (x1,x2) u := by
    unfold lowerEndpointWords; simp only [hpar, ↓reduceIte]
  have hEW2 : lowerEndpointWords (x2,x1) u = lowerEqualWords (x2,x1) u := by
    unfold lowerEndpointWords; simp only [hpar.symm, ↓reduceIte]
  have hsuf1 : ∀ b : Bool, lowerEndpointSuffix x1 u b = (if b then [2,1,3] else [3]) := by
    intro b; unfold lowerEndpointSuffix; rw [if_pos hfam]
  have hsuf2 : ∀ b : Bool, lowerEndpointSuffix x2 u b = (if b then [2,1,3] else [3]) := by
    intro b; unfold lowerEndpointSuffix; rw [if_pos hfam2]
  have hsh : lowerWidth (x1 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x2 ++ [3]) := by
    have h1 := width_append3_le x1 x2 htie hcd
    have h2 := width_pos (x2 ++ [3])
    linarith
  set s1 := lowerNaturalShort x1 u with hs1
  set s2 := lowerNaturalShort x2 u with hs2
  rw [equalWords_left (x1,x2) u hle1] at hEW1
  rw [equalWords_left (x2,x1) u hle2] at hEW2
  simp only [if_pos hfam, if_pos hfam2, ← hs1, ← hs2] at hEW1 hEW2
  rw [hsuf1, hsuf2] at hEW1
  rw [hsuf1, hsuf2] at hEW2
  have hshd : decide (lowerWidth (x1 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x2 ++ [3])) = true :=
    decide_eq_true hsh
  have hG1 := Gval_pos x1
  have hG2 := Gval_pos x2
  have hGge := Gval_ge_of_tie x1 x2 htie hcd
  have hsgn : sgnOf x1 = sgnOf x2 := by unfold sgnOf; rw [hpar]
  have hsq := sgnOf_sq x1
  have hlt := pL_lt_pS
  simp only [lowerEndpoint, hEW1, hEW2]
  by_cases hb : s1 = false ∧ s2 = false
  · obtain ⟨h1, h2⟩ := hb
    have hv1 : (s2 || (!s1 && !s2 &&
        decide (lowerWidth (x1 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x2 ++ [3])))) = true := by
      rw [h1, h2]; simp [hsh]
    have hv2 : (s1 || (!s2 && !s1 &&
        decide (lowerWidth (x2 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x1 ++ [3]))))
        = decide (lowerWidth (x2 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x1 ++ [3])) := by
      rw [h1, h2]; simp
    rw [hv1, hv2, h1, h2]
    by_cases hsh2 : lowerWidth (x2 ++ [3]) ≤ (7/5:ℝ) * lowerWidth (x1 ++ [3])
    · rw [decide_eq_true hsh2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pe_L, pe_L, pe_S, pe_S]
      have e1 : prefixEval x1 pL - prefixEval x1 pS = sgnOf x1 * (pL - pS) / Gval x1 := pe_LS x1
      have e2 : prefixEval x2 pL - prefixEval x2 pS = sgnOf x2 * (pL - pS) / Gval x2 := pe_LS x2
      rw [← hsgn] at e2
      have hexp : (4 + prefixEval x1 pL + prefixEval x2 pS)
          - (4 + prefixEval x2 pL + prefixEval x1 pS)
          = sgnOf x1 * (pL - pS) / Gval x1 - sgnOf x1 * (pL - pS) / Gval x2 := by linarith
      rw [hexp]
      exact sign_helper (sgnOf x1) (pL - pS) (Gval x1) (Gval x2) (sgnOf_cases x1)
        (by linarith) hG1 hG2 hGge
    · rw [decide_eq_false hsh2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [pe_L, pe_L, pe_S]
      have e2 : prefixEval x2 pL - prefixEval x2 pS = sgnOf x2 * (pL - pS) / Gval x2 := pe_LS x2
      rw [← hsgn] at e2
      have hexp : (4 + prefixEval x1 pL + prefixEval x2 pS)
          - (4 + prefixEval x2 pL + prefixEval x1 pL)
          = -(sgnOf x1 * (pL - pS) / Gval x2) := by linarith
      rw [hexp]
      exact sign_helper2 (sgnOf x1) (pL - pS) (Gval x2) (sgnOf_cases x1) (by linarith) hG2
  · have hff : (!s1 && !s2) = false := by
      rcases Bool.eq_false_or_eq_true s1 with h | h <;>
        rcases Bool.eq_false_or_eq_true s2 with h' | h' <;> simp_all
    have hff2 : (!s2 && !s1) = false := by
      rcases Bool.eq_false_or_eq_true s1 with h | h <;>
        rcases Bool.eq_false_or_eq_true s2 with h' | h' <;> simp_all
    simp only [hff, hff2, Bool.false_and, Bool.or_false]
    have : (4 + prefixEval (x1 ++ (if s1 = true then [2,1,3] else [3])) lowerTau
              + prefixEval (x2 ++ (if s2 = true then [2,1,3] else [3])) lowerTau)
         - (4 + prefixEval (x2 ++ (if s2 = true then [2,1,3] else [3])) lowerTau
              + prefixEval (x1 ++ (if s1 = true then [2,1,3] else [3])) lowerTau) = 0 := by ring
    rw [this, mul_zero]

/-! ### Obligation (A): normalisation only widens the cover -/

lemma norm_swap (a b : List ℕ+) (h : lowerWidth b ≠ lowerWidth a) :
    lowerNormalize (a,b) = lowerNormalize (b,a) := by
  classical
  by_cases hw : lowerWidth b ≤ lowerWidth a
  · have hw' : ¬ lowerWidth a ≤ lowerWidth b := fun hc => h (le_antisymm hw hc)
    simp [lowerNormalize, hw, hw']
  · have hw' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hw
    simp [lowerNormalize, hw, hw']

lemma endpoint_swap_equalParity (a b : List ℕ+) (u : Bool)
    (hpar : a.length % 2 = b.length % 2) (h : lowerWidth b ≠ lowerWidth a) :
    lowerEndpoint (a,b) u = lowerEndpoint (b,a) u := by
  classical
  have hE : lowerEndpointWords (a,b) u = lowerEqualWords (a,b) u := by
    simp [lowerEndpointWords, hpar]
  have hE' : lowerEndpointWords (b,a) u = lowerEqualWords (b,a) u := by
    simp [lowerEndpointWords, hpar.symm]
  have hn := norm_swap a b h
  by_cases hw : lowerWidth b ≤ lowerWidth a
  · have hw' : ¬ lowerWidth a ≤ lowerWidth b := fun hc => h (le_antisymm hw hc)
    simp only [lowerEndpoint, hE, hE', lowerEqualWords]
    simp only [hn]
    simp [hw, hw']
    ring
  · have hw' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hw
    simp only [lowerEndpoint, hE, hE', lowerEqualWords]
    simp only [hn]
    simp [hw, hw']
    ring

lemma endpoint_eq_of_words (P Q : LowerPair) (u : Bool)
    (h : lowerEndpointWords P u = lowerEndpointWords Q u) :
    lowerEndpoint P u = lowerEndpoint Q u := by
  simp only [lowerEndpoint, h]

lemma endpointWords_mixed_right (P : LowerPair) (u : Bool)
    (hpar : ¬ (P.1.length % 2 = P.2.length % 2))
    (hW : ¬ lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEndpointWords P u =
      (if u = decide (P.2.length % 2 = 0) then lowerEqualWords (P.1, P.2 ++ [1]) u
       else lowerNaturalWords P u) := by
  classical
  unfold lowerEndpointWords
  simp only [hpar, hW, ↓reduceIte]

lemma endpointWords_mixed_left (P : LowerPair) (u : Bool)
    (hpar : ¬ (P.1.length % 2 = P.2.length % 2))
    (hW : lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEndpointWords P u =
      (if u = decide (P.1.length % 2 = 0) then lowerEqualWords (P.1 ++ [1], P.2) u
       else lowerNaturalWords P u) := by
  classical
  unfold lowerEndpointWords
  simp only [hpar, hW, ↓reduceIte]

lemma endpoint_swap_natural (P : LowerPair) (u : Bool)
    (hpar : ¬ (P.1.length % 2 = P.2.length % 2))
    (hW : ¬ lowerWidth P.2 ≤ lowerWidth P.1)
    (hne : ¬ (u = decide (P.2.length % 2 = 0))) :
    lowerEndpoint P u = lowerEndpoint (P.2, P.1) u := by
  classical
  have hpar' : ¬ ((P.2,P.1).1.length % 2 = (P.2,P.1).2.length % 2) := fun h => hpar h.symm
  have hW' : lowerWidth (P.2,P.1).2 ≤ lowerWidth (P.2,P.1).1 := le_of_lt (lt_of_not_ge hW)
  have h1 := endpointWords_mixed_right P u hpar hW
  have h2 := endpointWords_mixed_left (P.2,P.1) u hpar' hW'
  rw [if_neg hne] at h1
  rw [if_neg hne] at h2
  simp only [lowerEndpoint, h1, h2, lowerNaturalWords]
  ring

/-- **Obligation (A).**  For a mixed-parity pair whose second word is not `[1]`,
normalisation can only enlarge the cover. -/
lemma cover_subset_normalize (p : LowerPair) (hm : lowerMixed p) (hp2 : p.2 ≠ [1]) :
    lowerCover p ⊆ lowerCover (lowerNormalize p) := by
  classical
  by_cases hW : lowerWidth p.2 ≤ lowerWidth p.1
  · rw [show lowerNormalize p = p from by simp [lowerNormalize, hW]]
  · have hn : lowerNormalize p = (p.2, p.1) := by simp [lowerNormalize, hW]
    rw [hn]
    have hpar : ¬ (p.1.length % 2 = p.2.length % 2) := hm
    have hpar' : ¬ ((p.2,p.1).1.length % 2 = (p.2,p.1).2.length % 2) := fun h => hpar h.symm
    have hW' : lowerWidth (p.2,p.1).2 ≤ lowerWidth (p.2,p.1).1 := le_of_lt (lt_of_not_ge hW)
    have hxpar : p.1.length % 2 = (p.2 ++ [1]).length % 2 := by
      simp only [List.length_append, List.length_singleton]; omega
    have hside : (lowerCD (p.2 ++ [1])).2 < 2*(lowerCD (p.2 ++ [1])).1 := by
      have hlt := cd_lt p.2 hp2
      have hone : ((1:ℕ+):ℕ) = 1 := rfl
      rw [lowerCD_append, hone, one_mul]
      omega
    have key : ∀ u : Bool, u = decide (p.2.length % 2 = 0) →
        0 ≤ sgnOf p.1 * (lowerEndpoint p u - lowerEndpoint (p.2,p.1) u) := by
      intro u hu
      have h1 := endpointWords_mixed_right p u hpar hW
      have h2 := endpointWords_mixed_left (p.2,p.1) u hpar' hW'
      rw [if_pos hu] at h1
      rw [if_pos hu] at h2
      have e1 : lowerEndpoint p u = lowerEndpoint (p.1, p.2 ++ [1]) u := by
        apply endpoint_eq_of_words
        rw [h1]
        unfold lowerEndpointWords
        simp only [hxpar, ↓reduceIte]
      have e2 : lowerEndpoint (p.2,p.1) u = lowerEndpoint (p.2 ++ [1], p.1) u := by
        apply endpoint_eq_of_words
        rw [h2]
        unfold lowerEndpointWords
        simp only [hxpar.symm, ↓reduceIte]
      rw [e1, e2]
      by_cases htie : lowerWidth p.1 = lowerWidth (p.2 ++ [1])
      · have hb : (!u) = decide (p.1.length % 2 = 0) := by
          rw [hu]
          rcases Nat.mod_two_eq_zero_or_one p.1.length with h1' | h1' <;>
            rcases Nat.mod_two_eq_zero_or_one p.2.length with h2' | h2' <;> simp_all
        have hfam : ((p.1.length % 2 = 0) = ((!u) = true)) := by
          rw [hb]; simp
        exact endpoint_tie_sign p.1 (p.2 ++ [1]) u hxpar hfam htie
          (cd_le_of_tie p.1 (p.2 ++ [1]) htie hside)
      · rw [endpoint_swap_equalParity p.1 (p.2 ++ [1]) u hxpar (fun h => htie h.symm)]
        simp
    have hother : ∀ u : Bool, ¬ (u = decide (p.2.length % 2 = 0)) →
        lowerEndpoint p u = lowerEndpoint (p.2,p.1) u := fun u hu =>
      endpoint_swap_natural p u hpar hW hu
    rcases Nat.mod_two_eq_zero_or_one p.1.length with he | he
    · have hvuf : decide (p.2.length % 2 = 0) = false := by
        simp only [decide_eq_false_iff_not]; omega
      have hs : sgnOf p.1 = 1 := by unfold sgnOf; rw [if_pos he]
      have hlo := key false (by rw [hvuf])
      rw [hs, one_mul] at hlo
      have hhi := hother true (by rw [hvuf]; simp)
      intro t ht
      rw [lowerCover, Set.mem_Icc] at ht ⊢
      exact ⟨by linarith [ht.1], by rw [← hhi]; exact ht.2⟩
    · have hvut : decide (p.2.length % 2 = 0) = true := by
        simp only [decide_eq_true_eq]; omega
      have hs : sgnOf p.1 = -1 := by unfold sgnOf; rw [if_neg (by omega)]
      have hhi := key true (by rw [hvut])
      rw [hs] at hhi
      have hlo := hother false (by rw [hvut]; simp)
      intro t ht
      rw [lowerCover, Set.mem_Icc] at ht ⊢
      exact ⟨by rw [← hlo]; exact ht.1, by linarith [ht.2]⟩

/-- Transport for obligation (B) in the branch where the spec pair is the NON-normalised
order: there the cover of the spec pair is contained in the cover of the real grandchild. -/
lemma cover_swap_of_wide (a b : List ℕ+)
    (hm : ¬ (a.length % 2 = b.length % 2)) (hb : b ≠ [1])
    (hW : ¬ lowerWidth b ≤ lowerWidth a) :
    lowerCover (a,b) ⊆ lowerCover (b,a) := by
  have h := cover_subset_normalize (a,b) hm hb
  rwa [show lowerNormalize (a,b) = (b,a) from by simp [lowerNormalize, hW]] at h

lemma ratio_le_one (w : List ℕ+) : lowerRatio w ≤ 1 := by
  rw [ratio_eq]
  have hd := (cd_pos w).2
  have hle : (rCD w).1 ≤ (rCD w).2 := by
    rw [rCD_fst, rCD_snd]; exact_mod_cast cd_le w
  exact (div_le_one hd).mpr hle


lemma alpha_lo : (263/1000 : ℝ) < lowerAlpha := by
  have h0 : (0:ℝ) ≤ lowerAlpha := ab_unit.1.1
  nlinarith [alpha_sq, h0]

lemma alpha_hi : lowerAlpha < (265/1000 : ℝ) := by
  have h0 : (0:ℝ) ≤ lowerAlpha := ab_unit.1.1
  nlinarith [alpha_sq, h0]

lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

lemma pe_unit (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1/(((a:ℕ):ℝ)+prefixEval w x) ∧ 1/(((a:ℕ):ℝ)+prefixEval w x) ≤ 1
    have hpos : 0 < ((a:ℕ):ℝ)+prefixEval w x := by linarith [ih.1]
    constructor
    · exact le_of_lt (div_pos (by norm_num) hpos)
    · apply (div_le_iff₀ hpos).2
      linarith [ih.1]

lemma width_append (w v : List ℕ+) : lowerWidth (w ++ v) =
    lowerWidth v / ((rCD w).2 ^ 2 *
      (1 + lowerRatio w * prefixEval v lowerAlpha) *
      (1 + lowerRatio w * prefixEval v lowerBeta)) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have ha := (pe_unit v lowerAlpha hA).1
  have hb := (pe_unit v lowerBeta hB).1
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  have hpos : 0 < (rCD w).2 ^ 2 * (1 + lowerRatio w * prefixEval v lowerBeta) *
      (1 + lowerRatio w * prefixEval v lowerAlpha) := by
    have : 0 ≤ lowerRatio w * prefixEval v lowerAlpha := mul_nonneg hp ha
    have : 0 ≤ lowerRatio w * prefixEval v lowerBeta := mul_nonneg hp hb
    positivity
  unfold lowerWidth
  rw [pe_append, pe_append, pe_diff w _ _ hb ha, abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul]
  ring

lemma pe3 (x : ℝ) : prefixEval [3] x = 1/(3+x) := by
  show (1:ℝ)/((((3:ℕ+):ℕ):ℝ) + x) = 1/(3+x)
  norm_num

lemma pe13 (x : ℝ) : prefixEval [1,3] x = 1/(1+1/(3+x)) := by
  show (1:ℝ)/((((1:ℕ+):ℕ):ℝ) + prefixEval [3] x) = _
  rw [pe3]; norm_num

lemma cd3 : (rCD [3]).2 = 3 ∧ lowerRatio [3] = 1/3 := by
  constructor
  · show (((lowerCD [3]).2 : ℕ) : ℝ) = 3
    norm_num [lowerCD]
  · show (((lowerCD [3]).1 : ℕ) : ℝ)/(((lowerCD [3]).2 : ℕ) : ℝ) = 1/3
    norm_num [lowerCD]

lemma cd13 : (rCD [1,3]).2 = 4 ∧ lowerRatio [1,3] = 1/4 := by
  constructor
  · show (((lowerCD [1,3]).2 : ℕ) : ℝ) = 4
    norm_num [lowerCD]
  · show (((lowerCD [1,3]).1 : ℕ) : ℝ)/(((lowerCD [1,3]).2 : ℕ) : ℝ) = 1/4
    norm_num [lowerCD]

/-! ### the `shorten` flag is off at a width tie -/

lemma shorten_key (al be ra rb Da Db : ℝ)
    (hal : 263/1000 < al) (hah : al < 265/1000) (hsq : 3*al^2 = 1 - 3*al) (hbe : be = 3*al)
    (hra0 : 0 ≤ ra) (hra1 : ra ≤ 1) (hrb0 : 0 ≤ rb) (hrb1 : rb ≤ 1)
    (hDa : 0 < Da) (hDb : 0 < Db)
    (hM : Da^2*(1+ra*al)*(1+ra*be) = Db^2*(1+rb*al)*(1+rb*be)) :
    (7/5:ℝ) * (Da^2 * ((3+al+ra)*(3+be+ra))) <
      Db^2 * ((4+al+rb*(3+al))*(4+be+rb*(3+be))) := by
  have hal0 : (0:ℝ) < al := by linarith
  subst hbe
  have hf : (3+al+ra)*(3+3*al+ra) ≤ 13*((1+ra*al)*(1+ra*(3*al))) := by
    have key : 13*((1+ra*al)*(1+ra*(3*al))) - (3+al+ra)*(3+3*al+ra)
        = 3 - 6*ra + 12*ra^2 + al*(48*ra - 39*ra^2 - 9) := by
      linear_combination (13*ra^2 - 1) * hsq
    have hq : (0:ℝ) < 3 - 6*ra + 12*ra^2 := by nlinarith [sq_nonneg (2*ra-1)]
    rcases le_or_gt (48*ra - 39*ra^2 - 9) 0 with hc | hc
    · have h1 : (0:ℝ) ≤ (265/1000 - al) * (-(48*ra - 39*ra^2 - 9)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [key, h1, sq_nonneg ra, hra0]
    · have h1 : (0:ℝ) < al * (48*ra - 39*ra^2 - 9) := mul_pos hal0 hc
      linarith [key, h1, hq]
  have hg : 20*((1+rb*al)*(1+rb*(3*al))) ≤ (4+al+rb*(3+al))*(4+3*al+rb*(3+3*al)) := by
    have key : (4+al+rb*(3+al))*(4+3*al+rb*(3+3*al)) - 20*((1+rb*al)*(1+rb*(3*al)))
        = -3 + 26*rb - 10*rb^2 + al*(13 - 58*rb + 69*rb^2) := by
      linear_combination (1 + 2*rb - 19*rb^2) * hsq
    have hpos : (0:ℝ) < 13 - 58*rb + 69*rb^2 := by nlinarith [sq_nonneg (138*rb - 58)]
    have h1 : (0:ℝ) ≤ (al - 263/1000) * (13 - 58*rb + 69*rb^2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [key, h1, sq_nonneg rb, hrb0]
  have hDa2 : (0:ℝ) < Da^2 := by positivity
  have hDb2 : (0:ℝ) < Db^2 := by positivity
  have e1 : Da^2 * ((3+al+ra)*(3+3*al+ra)) ≤ 13 * (Da^2*(1+ra*al)*(1+ra*(3*al))) := by
    nlinarith [hf, hDa2]
  have e2 : 20 * (Db^2*(1+rb*al)*(1+rb*(3*al)))
      ≤ Db^2 * ((4+al+rb*(3+al))*(4+3*al+rb*(3+3*al))) := by
    nlinarith [hg, hDb2]
  have hMpos : (0:ℝ) < Db^2*(1+rb*al)*(1+rb*(3*al)) := by
    have h1 : (0:ℝ) < 1 + rb*al := by nlinarith
    have h2 : (0:ℝ) < 1 + rb*(3*al) := by nlinarith
    exact mul_pos (mul_pos hDb2 h1) h2
  rw [hM] at e1
  linarith [e1, e2, hMpos]

lemma width3 : lowerWidth [3] = (lowerBeta - lowerAlpha)/((3+lowerAlpha)*(3+lowerBeta)) := by
  rw [width_eq, cd3.1, cd3.2]; congr 1; ring

lemma width13 : lowerWidth [1,3] = (lowerBeta - lowerAlpha)/((4+lowerAlpha)*(4+lowerBeta)) := by
  rw [width_eq, cd13.1, cd13.2]; congr 1; ring

lemma shorten_off (a b : List ℕ+) (h : lowerWidth a = lowerWidth b) :
    (7/5 : ℝ) * lowerWidth (b ++ [1,3]) < lowerWidth (a ++ [3]) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hal0 : (0:ℝ) < lowerAlpha := by linarith [alpha_lo]
  have hbe0 : (0:ℝ) < lowerBeta := by linarith [beta_eq]
  have hba : (0:ℝ) < lowerBeta - lowerAlpha := sub_pos.mpr hab
  have hra0 : 0 ≤ lowerRatio a := param_nonneg a
  have hrb0 : 0 ≤ lowerRatio b := param_nonneg b
  have hDa : (0:ℝ) < (rCD a).2 := (cd_pos a).2
  have hDb : (0:ℝ) < (rCD b).2 := (cd_pos b).2
  have h3a : (0:ℝ) < 3 + lowerAlpha := by linarith
  have h3b : (0:ℝ) < 3 + lowerBeta := by linarith
  have h4a : (0:ℝ) < 4 + lowerAlpha := by linarith
  have h4b : (0:ℝ) < 4 + lowerBeta := by linarith
  have hpa : (0:ℝ) < 1 + lowerRatio a * lowerAlpha := by nlinarith
  have hpb : (0:ℝ) < 1 + lowerRatio a * lowerBeta := by nlinarith
  have hqa : (0:ℝ) < 1 + lowerRatio b * lowerAlpha := by nlinarith
  have hqb : (0:ℝ) < 1 + lowerRatio b * lowerBeta := by nlinarith
  have hXpos : (0:ℝ) < (rCD a).2^2 * (1 + lowerRatio a * lowerAlpha) * (1 + lowerRatio a * lowerBeta) :=
    mul_pos (mul_pos (by positivity) hpa) hpb
  have hYpos : (0:ℝ) < (rCD b).2^2 * (1 + lowerRatio b * lowerAlpha) * (1 + lowerRatio b * lowerBeta) :=
    mul_pos (mul_pos (by positivity) hqa) hqb
  have hM : (rCD a).2^2 * (1 + lowerRatio a * lowerAlpha) * (1 + lowerRatio a * lowerBeta)
      = (rCD b).2^2 * (1 + lowerRatio b * lowerAlpha) * (1 + lowerRatio b * lowerBeta) := by
    have h' := h
    rw [width_eq a, width_eq b, div_eq_div_iff (ne_of_gt hXpos) (ne_of_gt hYpos)] at h'
    exact (mul_left_cancel₀ (ne_of_gt hba) h').symm
  have hVpos : (0:ℝ) < (rCD a).2^2 * ((3+lowerAlpha+lowerRatio a)*(3+lowerBeta+lowerRatio a)) := by
    apply mul_pos (by positivity); apply mul_pos <;> linarith
  have hUpos : (0:ℝ) < (rCD b).2^2 *
      ((4+lowerAlpha+lowerRatio b*(3+lowerAlpha))*(4+lowerBeta+lowerRatio b*(3+lowerBeta))) := by
    apply mul_pos (by positivity); apply mul_pos <;> nlinarith
  have hA3 : lowerWidth (a ++ [3]) = (lowerBeta - lowerAlpha) /
      ((rCD a).2^2 * ((3+lowerAlpha+lowerRatio a)*(3+lowerBeta+lowerRatio a))) := by
    rw [width_append, width3, pe3, pe3, div_div]
    congr 1
    field_simp
    try ring
  have hB13 : lowerWidth (b ++ [1,3]) = (lowerBeta - lowerAlpha) /
      ((rCD b).2^2 * ((4+lowerAlpha+lowerRatio b*(3+lowerAlpha))*(4+lowerBeta+lowerRatio b*(3+lowerBeta)))) := by
    rw [width_append, width13, pe13, pe13, div_div]
    congr 1
    field_simp
    ring
  have key2 := shorten_key lowerAlpha lowerBeta (lowerRatio a) (lowerRatio b) ((rCD a).2) ((rCD b).2)
    alpha_lo alpha_hi alpha_sq beta_eq hra0 (ratio_le_one a) hrb0 (ratio_le_one b) hDa hDb hM
  rw [hA3, hB13, mul_div_assoc']
  first
    | rw [div_lt_div_iff_of_pos hUpos hVpos]
    | rw [div_lt_div_iff hUpos hVpos]
    | rw [div_lt_div_iff₀ hUpos hVpos]
  nlinarith [mul_lt_mul_of_pos_left key2 hba]

/-! ### endpoint monotonicity in `upper` -/

lemma pS_lt_one : pS < 1 := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds; rw [pS_eq]; nlinarith

/-- every "lower" suffix value is below every "upper" suffix value -/
lemma small_lt_big (v w : ℝ) (hv : v = pL ∨ v = pS) (hw : w = pL ∨ w = pS) :
    v < 1/(1+w) := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  have hpL := pL_eq
  have hpS := pS_eq
  have hw1 : 0 ≤ w := by rcases hw with h | h <;> rw [h] <;> [exact pL_nonneg; exact pS_nonneg]
  have hwpos : (0:ℝ) < 1 + w := by linarith
  rw [lt_div_iff₀ hwpos]
  rcases hv with h | h <;> rcases hw with h' | h' <;> rw [h, h'] <;>
    simp only [hpL, hpS] <;> nlinarith

lemma pe_1cons (e : List ℕ+) (x : ℝ) : prefixEval ((1:ℕ+) :: e) x = 1/(1 + prefixEval e x) := by
  show (1:ℝ)/((((1:ℕ+):ℕ):ℝ) + prefixEval e x) = _
  norm_num

lemma esuf_small (x : List ℕ+) (u s : Bool) (h : (x.length % 2 = 0) = ((!u) = true)) :
    prefixEval (lowerEndpointSuffix x u s) lowerTau = if s then pS else pL := by
  unfold lowerEndpointSuffix
  rw [if_pos h]
  cases s <;> simp [pL, pS]

lemma esuf_big (x : List ℕ+) (u s : Bool) (h : ¬((x.length % 2 = 0) = ((!u) = true))) :
    prefixEval (lowerEndpointSuffix x u s) lowerTau =
      if s then 1/(1+pS) else 1/(1+pL) := by
  unfold lowerEndpointSuffix
  rw [if_neg h]
  cases s
  · show prefixEval ((1:ℕ+) :: [3]) lowerTau = _
    rw [pe_1cons]; simp [pL]
  · show prefixEval ((1:ℕ+) :: [2,1,3]) lowerTau = _
    rw [pe_1cons]; simp [pS]

lemma pe_lt (x : List ℕ+) (v v' : ℝ) (hv : 0 ≤ v) (hv' : 0 ≤ v')
    (h : 0 < sgnOf x * (v' - v)) : prefixEval x v < prefixEval x v' := by
  have hd := pe_diff x v' v hv' hv
  have hr := param_nonneg x
  have hD := (cd_pos x).2
  have h1 : 0 ≤ lowerRatio x * v := mul_nonneg hr hv
  have h2 : 0 ≤ lowerRatio x * v' := mul_nonneg hr hv'
  have hpos : 0 < (rCD x).2^2 * (1 + lowerRatio x * v') * (1 + lowerRatio x * v) := by positivity
  have := div_pos h hpos
  rw [← hd] at this
  linarith

noncomputable def esum (P : LowerPair) : ℝ := prefixEval P.1 lowerTau + prefixEval P.2 lowerTau
noncomputable def sideVal (x : List ℕ+) (u s : Bool) : ℝ :=
  prefixEval (x ++ lowerEndpointSuffix x u s) lowerTau

lemma sideVal_eq (x : List ℕ+) (u s : Bool) :
    sideVal x u s = prefixEval x (prefixEval (lowerEndpointSuffix x u s) lowerTau) := by
  unfold sideVal; rw [pe_append]

lemma sideVal_ext (x : List ℕ+) (u s : Bool) :
    sideVal (x ++ [1]) u s =
      prefixEval x (1/(1 + prefixEval (lowerEndpointSuffix (x ++ [1]) u s) lowerTau)) := by
  unfold sideVal
  rw [List.append_assoc, pe_append]
  congr 1
  rw [← pe_1cons]
  rfl

lemma len_ext (x : List ℕ+) : (x ++ [1]).length % 2 = (x.length + 1) % 2 := by simp

/-- lower suffix value comes first whatever the shortening flags -/
lemma sideA (x : List ℕ+) (s s' : Bool) : sideVal x false s < sideVal x true s' := by
  rw [sideVal_eq, sideVal_eq]
  rcases Nat.mod_two_eq_zero_or_one x.length with h | h
  · have hf : (x.length % 2 = 0) = (((!false)) = true) := by simp [h]
    have ht : ¬ ((x.length % 2 = 0) = ((!true) = true)) := by simp [h]
    rw [esuf_small x false s hf, esuf_big x true s' ht]
    have hsg : sgnOf x = 1 := by unfold sgnOf; rw [if_pos h]
    apply pe_lt
    · cases s <;> simp <;> [exact pL_nonneg; exact pS_nonneg]
    · cases s' <;> · have := pL_nonneg; have := pS_nonneg; positivity
    · rw [hsg]
      have := small_lt_big (if s then pS else pL) (if s' then pS else pL)
        (by cases s <;> simp) (by cases s' <;> simp)
      cases s' <;> simp at this ⊢ <;> linarith
  · have hf : ¬ ((x.length % 2 = 0) = (((!false)) = true)) := by simp [h]
    have ht : (x.length % 2 = 0) = ((!true) = true) := by simp [h]
    rw [esuf_big x false s hf, esuf_small x true s' ht]
    have hsg : sgnOf x = -1 := by unfold sgnOf; rw [if_neg (by omega)]
    apply pe_lt
    · cases s <;> · have := pL_nonneg; have := pS_nonneg; positivity
    · cases s' <;> simp <;> [exact pL_nonneg; exact pS_nonneg]
    · rw [hsg]
      have := small_lt_big (if s' then pS else pL) (if s then pS else pL)
        (by cases s' <;> simp) (by cases s <;> simp)
      cases s <;> cases s' <;> simp at this ⊢ <;> linarith

lemma sideB (x : List ℕ+) (h : x.length % 2 = 0) (s s' : Bool) :
    sideVal x false s < sideVal (x ++ [1]) true s' := by
  rw [sideVal_eq, sideVal_ext]
  have hf : (x.length % 2 = 0) = (((!false)) = true) := by simp [h]
  have ht : ((x ++ [1]).length % 2 = 0) = ((!true) = true) := by
    rw [len_ext]; simp; omega
  rw [esuf_small x false s hf, esuf_small (x ++ [1]) true s' ht]
  have hsg : sgnOf x = 1 := by unfold sgnOf; rw [if_pos h]
  apply pe_lt
  · cases s <;> simp <;> [exact pL_nonneg; exact pS_nonneg]
  · cases s' <;> · have := pL_nonneg; have := pS_nonneg; positivity
  · rw [hsg]
    have := small_lt_big (if s then pS else pL) (if s' then pS else pL)
      (by cases s <;> simp) (by cases s' <;> simp)
    linarith

lemma sideC (x : List ℕ+) (h : x.length % 2 = 1) (s s' : Bool) :
    sideVal (x ++ [1]) false s < sideVal x true s' := by
  rw [sideVal_ext, sideVal_eq]
  have hf : ((x ++ [1]).length % 2 = 0) = (((!false)) = true) := by
    rw [len_ext]; simp; omega
  have ht : (x.length % 2 = 0) = ((!true) = true) := by simp [h]
  rw [esuf_small (x ++ [1]) false s hf, esuf_small x true s' ht]
  have hsg : sgnOf x = -1 := by unfold sgnOf; rw [if_neg (by omega)]
  apply pe_lt
  · cases s <;> · have := pL_nonneg; have := pS_nonneg; positivity
  · cases s' <;> simp <;> [exact pL_nonneg; exact pS_nonneg]
  · rw [hsg]
    have := small_lt_big (if s' then pS else pL) (if s then pS else pL)
      (by cases s' <;> simp) (by cases s <;> simp)
    linarith

lemma equalWords_right (P : LowerPair) (u : Bool) (hW : ¬ lowerWidth P.2 ≤ lowerWidth P.1) :
    lowerEqualWords P u =
      (P.1 ++ lowerEndpointSuffix P.1 u (lowerNaturalShort P.1 u ||
         (!lowerNaturalShort P.2 u && !lowerNaturalShort P.1 u &&
           decide (lowerWidth (P.2 ++ (if (P.2.length % 2 = 0) = (!u) then [3] else [1,3])) ≤
             (7/5 : ℝ) * lowerWidth (P.1 ++ (if (P.2.length % 2 = 0) = (!u) then [3] else [1,3]))))),
       P.2 ++ lowerEndpointSuffix P.2 u (lowerNaturalShort P.2 u)) := by
  unfold lowerEqualWords lowerNormalize
  simp only [hW, ↓reduceIte]

lemma equalWords_esum (P : LowerPair) (u : Bool) :
    ∃ s s' : Bool, esum (lowerEqualWords P u) = sideVal P.1 u s + sideVal P.2 u s' := by
  classical
  by_cases hw : lowerWidth P.2 ≤ lowerWidth P.1
  · rw [equalWords_left P u hw]; exact ⟨_, _, rfl⟩
  · rw [equalWords_right P u hw]; exact ⟨_, _, rfl⟩

lemma naturalWords_esum (P : LowerPair) (u : Bool) :
    esum (lowerNaturalWords P u) =
      sideVal P.1 u (lowerNaturalShort P.1 u) + sideVal P.2 u (lowerNaturalShort P.2 u) := rfl

lemma endpoint_esum (P : LowerPair) (u : Bool) :
    lowerEndpoint P u = 4 + esum (lowerEndpointWords P u) := by
  unfold lowerEndpoint esum; ring

set_option maxHeartbeats 800000 in
lemma endpoint_lt (X : LowerPair) : lowerEndpoint X false < lowerEndpoint X true := by
  classical
  rw [endpoint_esum, endpoint_esum]
  have main : esum (lowerEndpointWords X false) < esum (lowerEndpointWords X true) := by
    by_cases hpar : X.1.length % 2 = X.2.length % 2
    · have e0 : lowerEndpointWords X false = lowerEqualWords X false := by
        unfold lowerEndpointWords; simp only [hpar, ↓reduceIte]
      have e1 : lowerEndpointWords X true = lowerEqualWords X true := by
        unfold lowerEndpointWords; simp only [hpar, ↓reduceIte]
      obtain ⟨a, b, ha⟩ := equalWords_esum X false
      obtain ⟨c, d, hc⟩ := equalWords_esum X true
      rw [e0, e1, ha, hc]
      linarith [sideA X.1 a c, sideA X.2 b d]
    · by_cases hW : lowerWidth X.2 ≤ lowerWidth X.1
      · have shape : ∀ u : Bool, lowerEndpointWords X u =
            (if u = decide (X.1.length % 2 = 0) then lowerEqualWords (X.1 ++ [1], X.2) u
             else lowerNaturalWords X u) := by
          intro u; unfold lowerEndpointWords; simp only [hpar, hW, ↓reduceIte]
        rcases Nat.mod_two_eq_zero_or_one X.1.length with h | h
        · have hv : decide (X.1.length % 2 = 0) = true := by simp [h]
          rw [shape false, shape true, hv]
          simp only [Bool.false_eq_true, ↓reduceIte, if_pos]
          obtain ⟨c, d, hc⟩ := equalWords_esum (X.1 ++ [1], X.2) true
          rw [naturalWords_esum, hc]
          exact add_lt_add (sideB X.1 h _ c) (sideA X.2 _ d)
        · have hv : decide (X.1.length % 2 = 0) = false := by simp; omega
          rw [shape false, shape true, hv]
          simp only [Bool.true_eq_false, ↓reduceIte, if_pos]
          obtain ⟨a, b, ha⟩ := equalWords_esum (X.1 ++ [1], X.2) false
          rw [naturalWords_esum, ha]
          exact add_lt_add (sideC X.1 h a _) (sideA X.2 b _)
      · have shape : ∀ u : Bool, lowerEndpointWords X u =
            (if u = decide (X.2.length % 2 = 0) then lowerEqualWords (X.1, X.2 ++ [1]) u
             else lowerNaturalWords X u) := by
          intro u; unfold lowerEndpointWords; simp only [hpar, hW, ↓reduceIte]
        rcases Nat.mod_two_eq_zero_or_one X.2.length with h | h
        · have hv : decide (X.2.length % 2 = 0) = true := by simp [h]
          rw [shape false, shape true, hv]
          simp only [Bool.false_eq_true, ↓reduceIte, if_pos]
          obtain ⟨c, d, hc⟩ := equalWords_esum (X.1, X.2 ++ [1]) true
          rw [naturalWords_esum, hc]
          exact add_lt_add (sideA X.1 _ c) (sideB X.2 h _ d)
        · have hv : decide (X.2.length % 2 = 0) = false := by simp; omega
          rw [shape false, shape true, hv]
          simp only [Bool.true_eq_false, ↓reduceIte, if_pos]
          obtain ⟨a, b, ha⟩ := equalWords_esum (X.1, X.2 ++ [1]) false
          rw [naturalWords_esum, ha]
          exact add_lt_add (sideA X.1 a _) (sideC X.2 h b _)
  linarith

/-! ### the shallow tie `lowerWidth a = lowerWidth b` is harmless -/

lemma prop_eq_bool (P : Prop) [Decidable P] (b : Bool) : (P = (b = true)) ↔ decide P = b := by
  cases b <;> simp

lemma suffix31_snoc1 (x : List ℕ+) :
    (([3,1] : List ℕ+) <:+ x ++ [1]) ↔ (([3] : List ℕ+) <:+ x) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h2 : (t ++ [3]) ++ [1] = x ++ [1] := by simpa using ht
    exact List.append_cancel_right h2
  · rintro ⟨t, ht⟩
    exact ⟨t, by simp [← ht]⟩

lemma width_single (c : ℕ+) : lowerWidth [c] =
    (lowerBeta - lowerAlpha)/((((c:ℕ):ℝ)+lowerAlpha)*(((c:ℕ):ℝ)+lowerBeta)) := by
  have hc : (0:ℝ) < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have h1 : (rCD [c]).2 = ((c:ℕ):ℝ) := by
    show (((lowerCD [c]).2 : ℕ) : ℝ) = _
    simp [lowerCD]
  have h2 : lowerRatio [c] = 1/((c:ℕ):ℝ) := by
    show (((lowerCD [c]).1 : ℕ) : ℝ)/(((lowerCD [c]).2 : ℕ) : ℝ) = _
    simp [lowerCD]
  rw [width_eq, h1, h2]
  congr 1
  field_simp
  try ring

lemma width_snoc_lt (w : List ℕ+) (c : ℕ+) : lowerWidth (w ++ [c]) < lowerWidth w := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hc : (1:ℝ) ≤ ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hr := param_nonneg w
  have hD := (cd_pos w).2
  have hal0 : (0:ℝ) < lowerAlpha := by linarith [alpha_lo]
  have hca : (0:ℝ) < ((c:ℕ):ℝ) + lowerAlpha := by linarith
  have hcb : (0:ℝ) < ((c:ℕ):ℝ) + lowerBeta := by linarith [hB.1]
  have hpa : (0:ℝ) < 1 + lowerRatio w * lowerAlpha := by nlinarith
  have hpb : (0:ℝ) < 1 + lowerRatio w * lowerBeta := by nlinarith
  have hE : lowerWidth (w ++ [c]) = (lowerBeta - lowerAlpha) /
      ((rCD w).2^2 * ((((c:ℕ):ℝ)+lowerAlpha+lowerRatio w)*(((c:ℕ):ℝ)+lowerBeta+lowerRatio w))) := by
    rw [width_append, width_single, pe_single, pe_single, div_div]
    congr 1
    field_simp
    try ring
  have hF : lowerWidth w = (lowerBeta - lowerAlpha) /
      ((rCD w).2^2 * ((1 + lowerRatio w * lowerAlpha)*(1 + lowerRatio w * lowerBeta))) := by
    rw [width_eq]; congr 1; ring
  have hq1 : (0:ℝ) < (rCD w).2^2 * ((((c:ℕ):ℝ)+lowerAlpha+lowerRatio w)*(((c:ℕ):ℝ)+lowerBeta+lowerRatio w)) := by
    apply mul_pos (by positivity); apply mul_pos <;> linarith
  have hq2 : (0:ℝ) < (rCD w).2^2 * ((1 + lowerRatio w * lowerAlpha)*(1 + lowerRatio w * lowerBeta)) :=
    mul_pos (by positivity) (mul_pos hpa hpb)
  have hcmp : (1 + lowerRatio w * lowerAlpha)*(1 + lowerRatio w * lowerBeta)
      < (((c:ℕ):ℝ)+lowerAlpha+lowerRatio w)*(((c:ℕ):ℝ)+lowerBeta+lowerRatio w) := by
    have hdec : (((c:ℕ):ℝ)+lowerAlpha+lowerRatio w)*(((c:ℕ):ℝ)+lowerBeta+lowerRatio w)
        - (1 + lowerRatio w * lowerAlpha)*(1 + lowerRatio w * lowerBeta)
        = (((c:ℕ):ℝ)*((c:ℕ):ℝ) - 1) + ((c:ℕ):ℝ)*(lowerAlpha+lowerBeta)
          + 2*((c:ℕ):ℝ)*lowerRatio w + lowerAlpha*lowerBeta
          + lowerRatio w^2*(1 - lowerAlpha*lowerBeta) := by ring
    have t1 : (0:ℝ) ≤ ((c:ℕ):ℝ)*((c:ℕ):ℝ) - 1 := by nlinarith
    have t2 : (0:ℝ) < ((c:ℕ):ℝ)*(lowerAlpha+lowerBeta) := by nlinarith [hB.1]
    have t3 : (0:ℝ) ≤ 2*((c:ℕ):ℝ)*lowerRatio w := by nlinarith [hB.1]
    have t4 : (0:ℝ) ≤ lowerAlpha*lowerBeta := by nlinarith [hB.1]
    have t5 : (0:ℝ) ≤ lowerRatio w^2*(1 - lowerAlpha*lowerBeta) := by
      have : lowerAlpha*lowerBeta ≤ 1 := by nlinarith [hA.1, hA.2, hB.1, hB.2]
      nlinarith [sq_nonneg (lowerRatio w)]
    linarith
  rw [hE, hF]
  apply div_lt_div_of_pos_left (sub_pos.mpr hab) hq2
  exact mul_lt_mul_of_pos_left hcmp (by positivity)

lemma sideVal_ext_eq (x : List ℕ+) (u : Bool) (hu : u = decide (x.length % 2 = 0)) :
    sideVal (x ++ [1]) u (lowerNaturalShort (x ++ [1]) u)
      = sideVal x u (lowerNaturalShort x u) := by
  classical
  have hd1 : decide ((x ++ [1]).length % 2 = 0) = !u := by
    rw [hu, len_ext]
    rcases Nat.mod_two_eq_zero_or_one x.length with h | h <;> simp [h] <;> omega
  have hd2 : decide (x.length % 2 = 0) ≠ !u := by
    rw [hu]; cases hb : decide (x.length % 2 = 0) <;> simp
  have hc1 : ((x ++ [1]).length % 2 = 0) = ((!u) = true) := (prop_eq_bool _ _).mpr hd1
  have hc2 : ¬ ((x.length % 2 = 0) = ((!u) = true)) := fun h => hd2 ((prop_eq_bool _ _).mp h)
  have hs : lowerNaturalShort (x ++ [1]) u = lowerNaturalShort x u := by
    unfold lowerNaturalShort
    rw [if_pos hc1, if_neg hc2]
    congr 1
    simp only [lowerEnds, eq_iff_iff]
    exact suffix31_snoc1 x
  unfold sideVal
  congr 1
  unfold lowerEndpointSuffix
  rw [if_pos hc1, if_neg hc2, hs]
  cases lowerNaturalShort x u <;> simp

lemma eq_nat_shallow (x y : List ℕ+) (u : Bool)
    (hpar : ¬ (x.length % 2 = y.length % 2))
    (hW : lowerWidth x = lowerWidth y)
    (hu : u = decide (x.length % 2 = 0)) :
    esum (lowerEqualWords (x ++ [1], y) u) = esum (lowerNaturalWords (x, y) u) := by
  classical
  have hlt : lowerWidth (x ++ [1]) < lowerWidth y := by
    rw [← hW]; exact width_snoc_lt x 1
  have hWr : ¬ lowerWidth ((x ++ [1], y) : LowerPair).2 ≤ lowerWidth ((x ++ [1], y) : LowerPair).1 := by
    simp only [not_le]; exact hlt
  have hdy : decide (y.length % 2 = 0) = !u := by
    rw [hu]
    rcases Nat.mod_two_eq_zero_or_one x.length with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one y.length with h' | h' <;> simp_all <;> omega
  have hcy : (y.length % 2 = 0) = ((!u) = true) := (prop_eq_bool _ _).mpr hdy
  rw [equalWords_right _ u hWr]
  simp only [if_pos hcy]
  have hsh : decide (lowerWidth (y ++ [3]) ≤ (7/5 : ℝ) * lowerWidth ((x ++ [1]) ++ [3])) = false := by
    apply decide_eq_false
    rw [List.append_assoc]
    exact not_le.mpr (shorten_off y x hW.symm)
  rw [hsh]
  simp only [Bool.and_false, Bool.or_false]
  unfold esum
  show sideVal (x ++ [1]) u (lowerNaturalShort (x ++ [1]) u) + sideVal y u (lowerNaturalShort y u)
    = sideVal x u (lowerNaturalShort x u) + sideVal y u (lowerNaturalShort y u)
  rw [sideVal_ext_eq x u hu]

lemma endpoint_swap_shallow (a b : List ℕ+) (u : Bool)
    (hpar : ¬ (a.length % 2 = b.length % 2)) (hW : lowerWidth a = lowerWidth b) :
    lowerEndpoint (a,b) u = lowerEndpoint (b,a) u := by
  classical
  have hpar' : ¬ (b.length % 2 = a.length % 2) := fun h => hpar h.symm
  have hle : lowerWidth ((a,b) : LowerPair).2 ≤ lowerWidth ((a,b) : LowerPair).1 := le_of_eq hW.symm
  have hle' : lowerWidth ((b,a) : LowerPair).2 ≤ lowerWidth ((b,a) : LowerPair).1 := le_of_eq hW
  have shapeA := endpointWords_mixed_left (a,b) u hpar hle
  have shapeB := endpointWords_mixed_left (b,a) u hpar' hle'
  simp only at shapeA shapeB
  rw [endpoint_esum, endpoint_esum, shapeA, shapeB]
  have hne : decide (b.length % 2 = 0) = !decide (a.length % 2 = 0) := by
    rcases Nat.mod_two_eq_zero_or_one a.length with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one b.length with h' | h' <;> simp_all <;> omega
  have hswap : esum (lowerNaturalWords ((b,a) : LowerPair) u)
      = esum (lowerNaturalWords ((a,b) : LowerPair) u) := by
    unfold esum lowerNaturalWords; simp only; ring
  by_cases hu : u = decide (a.length % 2 = 0)
  · have hu2 : ¬ (u = decide (b.length % 2 = 0)) := by rw [hne, hu]; simp
    rw [if_pos hu, if_neg hu2, hswap]
    exact congrArg (fun z => 4 + z) (eq_nat_shallow a b u hpar hW hu)
  · have hu2 : u = decide (b.length % 2 = 0) := by
      rw [hne]
      cases hb : decide (a.length % 2 = 0) <;> cases u <;> simp_all
    rw [if_neg hu, if_pos hu2, eq_nat_shallow b a u hpar' hW.symm hu2, hswap]

/-! ### the mixed-pair swap transport -/

lemma endpoint_mixed_left_ext (a b : List ℕ+) (u : Bool)
    (hpar : ¬ (a.length % 2 = b.length % 2))
    (hW : lowerWidth b ≤ lowerWidth a)
    (hu : u = decide (a.length % 2 = 0)) :
    lowerEndpoint (a,b) u = lowerEndpoint (a ++ [1], b) u := by
  apply endpoint_eq_of_words
  rw [endpointWords_mixed_left (a,b) u hpar hW, if_pos hu]
  have hxpar : (a ++ [1]).length % 2 = b.length % 2 := by
    simp only [List.length_append, List.length_singleton]; omega
  unfold lowerEndpointWords
  simp only [hxpar, ↓reduceIte]

lemma endpoint_mixed_right_ext (a b : List ℕ+) (u : Bool)
    (hpar : ¬ (a.length % 2 = b.length % 2))
    (hW : ¬ lowerWidth a ≤ lowerWidth b)
    (hu : u = decide (a.length % 2 = 0)) :
    lowerEndpoint (b,a) u = lowerEndpoint (b, a ++ [1]) u := by
  apply endpoint_eq_of_words
  have hpar' : ¬ (((b,a) : LowerPair).1.length % 2 = ((b,a) : LowerPair).2.length % 2) :=
    fun h => hpar h.symm
  rw [endpointWords_mixed_right (b,a) u hpar' hW, if_pos hu]
  have hxpar : b.length % 2 = (a ++ [1]).length % 2 := by
    simp only [List.length_append, List.length_singleton]; omega
  unfold lowerEndpointWords
  simp only [hxpar, ↓reduceIte]

lemma endpoint_mixed_nat (a b : List ℕ+) (u : Bool)
    (hpar : ¬ (a.length % 2 = b.length % 2))
    (hW : lowerWidth b < lowerWidth a)
    (hu : ¬ (u = decide (a.length % 2 = 0))) :
    lowerEndpoint (a,b) u = lowerEndpoint (b,a) u := by
  rw [endpoint_esum, endpoint_esum,
      endpointWords_mixed_left (a,b) u hpar (le_of_lt hW),
      endpointWords_mixed_right (b,a) u (fun h => hpar h.symm) (not_le.mpr hW),
      if_neg hu, if_neg hu]
  unfold esum lowerNaturalWords
  simp only
  ring

/-- **The swap transport for a mixed-parity pair.**  The only hypothesis beyond
admissibility hygiene is that at an exact deep tie the extended left word has the
smaller numerator continuant. -/
lemma cover_swap_mixed (a b : List ℕ+)
    (hpar : ¬ (a.length % 2 = b.length % 2)) (hb : b ≠ [1])
    (hgood : lowerWidth (a ++ [1]) = lowerWidth b → (lowerCD (a ++ [1])).1 ≤ (lowerCD b).1) :
    lowerCover (a,b) ⊆ lowerCover (b,a) := by
  classical
  rcases lt_trichotomy (lowerWidth b) (lowerWidth a) with hW | hW | hW
  · have hxpar : (a ++ [1]).length % 2 = b.length % 2 := by
      simp only [List.length_append, List.length_singleton]; omega
    have hnat : ∀ u : Bool, ¬ (u = decide (a.length % 2 = 0)) →
        lowerEndpoint (a,b) u = lowerEndpoint (b,a) u :=
      fun u hu => endpoint_mixed_nat a b u hpar hW hu
    have hext : ∀ u : Bool, u = decide (a.length % 2 = 0) →
        lowerEndpoint (a,b) u = lowerEndpoint (a ++ [1], b) u ∧
        lowerEndpoint (b,a) u = lowerEndpoint (b, a ++ [1]) u := by
      intro u hu
      exact ⟨endpoint_mixed_left_ext a b u hpar (le_of_lt hW) hu,
             endpoint_mixed_right_ext a b u hpar (not_le.mpr hW) hu⟩
    by_cases hd : lowerWidth (a ++ [1]) = lowerWidth b
    · have hcd := hgood hd
      have hkey : ∀ u : Bool, u = decide (a.length % 2 = 0) →
          0 ≤ sgnOf (a ++ [1]) * (lowerEndpoint (a,b) u - lowerEndpoint (b,a) u) := by
        intro u hu
        obtain ⟨e1, e2⟩ := hext u hu
        rw [e1, e2]
        have hfam : (((a ++ [1]).length % 2 = 0) = ((!u) = true)) := by
          apply (prop_eq_bool _ _).mpr
          rw [hu]
          simp only [List.length_append, List.length_singleton]
          rcases Nat.mod_two_eq_zero_or_one a.length with h | h <;> simp [h] <;> omega
        exact endpoint_tie_sign (a ++ [1]) b u hxpar hfam hd hcd
      rcases Nat.mod_two_eq_zero_or_one a.length with h | h
      · have hv : decide (a.length % 2 = 0) = true := by simp [h]
        have hs : sgnOf (a ++ [1]) = -1 := by
          rw [sgnOf_append]; unfold sgnOf; rw [if_pos h]; try norm_num
        have hhi := hkey true (by rw [hv])
        rw [hs] at hhi
        have hlo := hnat false (by rw [hv]; simp)
        intro t ht
        rw [lowerCover, Set.mem_Icc] at ht ⊢
        exact ⟨by rw [← hlo]; exact ht.1, by linarith [ht.2]⟩
      · have hv : decide (a.length % 2 = 0) = false := by simp; omega
        have hs : sgnOf (a ++ [1]) = 1 := by
          rw [sgnOf_append]; unfold sgnOf; rw [if_neg (by omega)]; try norm_num
        have hlo := hkey false (by rw [hv])
        rw [hs, one_mul] at hlo
        have hhi := hnat true (by rw [hv]; simp)
        intro t ht
        rw [lowerCover, Set.mem_Icc] at ht ⊢
        exact ⟨by linarith [ht.1], by rw [← hhi]; exact ht.2⟩
    · have heq : ∀ u : Bool, lowerEndpoint (a,b) u = lowerEndpoint (b,a) u := by
        intro u
        by_cases hu : u = decide (a.length % 2 = 0)
        · obtain ⟨e1, e2⟩ := hext u hu
          rw [e1, e2]
          exact endpoint_swap_equalParity (a ++ [1]) b u hxpar (fun hc => hd hc.symm)
        · exact hnat u hu
      intro t ht
      rw [lowerCover, Set.mem_Icc] at ht ⊢
      exact ⟨by rw [← heq false]; exact ht.1, by rw [← heq true]; exact ht.2⟩
  · intro t ht
    rw [lowerCover, Set.mem_Icc] at ht ⊢
    exact ⟨by rw [← endpoint_swap_shallow a b false hpar hW.symm]; exact ht.1,
           by rw [← endpoint_swap_shallow a b true hpar hW.symm]; exact ht.2⟩
  · exact cover_swap_of_wide a b hpar hb (not_le.mpr hW)

/-! ### goodness of a child from the two normalisation specs -/

lemma scale_pos (q : LowerPair) : (0:ℝ) < lowerScale q := by
  show 0 < ((lowerCD q.1).2 : ℝ)^2 / ((lowerCD q.2).2 : ℝ)^2
  have h1 : (0:ℝ) < ((lowerCD q.1).2 : ℝ) := by exact_mod_cast cd_den_pos q.1
  have h2 : (0:ℝ) < ((lowerCD q.2).2 : ℝ) := by exact_mod_cast cd_den_pos q.2
  positivity

lemma wide_iff (q w : LowerPair) :
    (lowerScale q ≤ certThresholdVal (lowerHistoryWH w) (lowerRatio q.1) (lowerRatio q.2))
      ↔ lowerWidth (q.2 ++ w.2) ≤ lowerWidth (q.1 ++ w.1) := by
  rw [LowerDev.wh_key]
  have hq := scale_pos q
  have h2 := width_pos (q.2 ++ w.2)
  rw [le_mul_iff_one_le_right hq, one_le_div h2]

lemma good_of_overlap (G1 G2 A1 A2 : LowerPair)
    (h1 : lowerEndpoint A1 false < lowerEndpoint A2 true)
    (h2 : lowerEndpoint A2 false < lowerEndpoint A1 true)
    (s1 : lowerCover A1 ⊆ lowerCover G1) (s2 : lowerCover A2 ⊆ lowerCover G2) :
    (lowerCover G1 ∩ lowerCover G2).Nonempty := by
  have e1 := endpoint_lt A1
  have e2 := endpoint_lt A2
  refine ⟨max (lowerEndpoint A1 false) (lowerEndpoint A2 false), s1 ?_, s2 ?_⟩
  · rw [lowerCover, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le (le_of_lt e1) (le_of_lt h2)⟩
  · rw [lowerCover, Set.mem_Icc]
    exact ⟨le_max_right _ _, max_le (le_of_lt h1) (le_of_lt e2)⟩

lemma child_good_core (c : LowerPair)
    (hF : lowerWidth c.2 ≤ lowerWidth c.1 →
       lowerEndpoint (c.1 ++ [1], c.2) false < lowerEndpoint (c.1 ++ [2], c.2) true ∧
       lowerEndpoint (c.1 ++ [2], c.2) false < lowerEndpoint (c.1 ++ [1], c.2) true)
    (hT : lowerWidth c.1 < lowerWidth c.2 →
       (lowerEndpoint (c.1, c.2 ++ [1]) false < lowerEndpoint (c.1, c.2 ++ [2]) true ∧
        lowerEndpoint (c.1, c.2 ++ [2]) false < lowerEndpoint (c.1, c.2 ++ [1]) true) ∧
       (lowerCover (c.1, c.2 ++ [1]) ⊆ lowerCover (c.2 ++ [1], c.1) ∧
        lowerCover (c.1, c.2 ++ [2]) ⊆ lowerCover (c.2 ++ [2], c.1))) :
    lowerGood c := by
  classical
  unfold lowerGood
  by_cases hw : lowerWidth c.2 ≤ lowerWidth c.1
  · have hn : lowerNormalize c = c := by simp [lowerNormalize, hw]
    obtain ⟨h1, h2⟩ := hF hw
    have g1 : lowerChild c ([1],[]) = (c.1 ++ [1], c.2) := by simp [lowerChild, hn]
    have g2 : lowerChild c ([2],[]) = (c.1 ++ [2], c.2) := by simp [lowerChild, hn]
    rw [g1, g2]
    exact good_of_overlap _ _ _ _ h1 h2 (subset_refl _) (subset_refl _)
  · have hlt : lowerWidth c.1 < lowerWidth c.2 := lt_of_not_ge hw
    have hn : lowerNormalize c = (c.2, c.1) := by simp [lowerNormalize, hw]
    obtain ⟨⟨h1, h2⟩, hsub⟩ := hT hlt
    have g1 : lowerChild c ([1],[]) = (c.2 ++ [1], c.1) := by simp [lowerChild, hn]
    have g2 : lowerChild c ([2],[]) = (c.2 ++ [2], c.1) := by simp [lowerChild, hn]
    rw [g1, g2]
    exact good_of_overlap _ _ _ _ h1 h2 hsub.1 hsub.2

lemma pair_overlap_of_specs (p : LowerPair) (X Y : LowerPair)
    (h1 : section14LocalEndpoint p Y false < section14LocalEndpoint p X true)
    (h2 : section14LocalEndpoint p X false < section14LocalEndpoint p Y true) :
    lowerEndpoint ((lowerNormalize p).1 ++ X.1, (lowerNormalize p).2 ++ X.2) false
        < lowerEndpoint ((lowerNormalize p).1 ++ Y.1, (lowerNormalize p).2 ++ Y.2) true ∧
    lowerEndpoint ((lowerNormalize p).1 ++ Y.1, (lowerNormalize p).2 ++ Y.2) false
        < lowerEndpoint ((lowerNormalize p).1 ++ X.1, (lowerNormalize p).2 ++ X.2) true := by
  classical
  unfold section14LocalEndpoint at h1 h2
  simp only [Bool.not_false, Bool.not_true] at h1 h2
  by_cases hpar : (lowerNormalize p).1.length % 2 = 0
  · simp only [if_pos hpar] at h1 h2
    exact ⟨h2, h1⟩
  · simp only [if_neg hpar] at h1 h2
    constructor <;> linarith

lemma ratio_snoc (w : List ℕ+) (c : ℕ+) :
    lowerRatio (w ++ [c]) = 1/(((c:ℕ):ℝ) + lowerRatio w) := by
  have hd := (cd_pos w).2
  have hc := (cd_pos w).1
  have hcc : (0:ℝ) < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hden : (0:ℝ) < ((c:ℕ):ℝ) + lowerRatio w := by
    have := param_nonneg w; linarith
  rw [ratio_eq, cd_append, ratio_eq]
  simp only
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

lemma ratio_bounds_snoc (w : List ℕ+) (c : ℕ+) (lo hi : ℝ)
    (h0 : 0 ≤ lo) (h1 : lo ≤ lowerRatio w) (h2 : lowerRatio w ≤ hi) :
    1/(((c:ℕ):ℝ) + hi) ≤ lowerRatio (w ++ [c]) ∧
      lowerRatio (w ++ [c]) ≤ 1/(((c:ℕ):ℝ) + lo) := by
  have hcc : (0:ℝ) < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hr := param_nonneg w
  have d1 : (0:ℝ) < ((c:ℕ):ℝ) + lo := by linarith
  have d2 : (0:ℝ) < ((c:ℕ):ℝ) + lowerRatio w := by linarith
  have d3 : (0:ℝ) < ((c:ℕ):ℝ) + hi := by linarith
  rw [ratio_snoc]
  constructor
  · apply one_div_le_one_div_of_le d2; linarith
  · apply one_div_le_one_div_of_le d1; linarith

/-! ### the three `lowerTheta` values entering `lowerH p 5` -/

lemma sqrt3_tight : (1732/1000 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (17321/10000 : ℝ) := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hnn := Real.sqrt_nonneg 3
  constructor <;> nlinarith [h3, hnn]

lemma pL_bounds : (2679/10000 : ℝ) < pL ∧ pL < (268/1000 : ℝ) := by
  obtain ⟨h1, h2⟩ := sqrt3_tight
  rw [pL_eq]; constructor <;> linarith

lemma pS_bounds : (3585/10000 : ℝ) < pS ∧ pS < (3586/10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := sqrt3_tight
  rw [pS_eq]; constructor <;> linarith

lemma theta63_eq : lowerTheta 63 = 1/(2 + pL) := by
  show prefixEval [2,3] lowerTau = _
  show (1:ℝ)/((((2:ℕ+):ℕ):ℝ) + prefixEval [3] lowerTau) = _
  norm_num [pL]

lemma theta70_eq : lowerTheta 70 = 1/(1 + 1/(1 + pS)) := by
  show prefixEval [1,1,2,1,3] lowerTau = _
  show (1:ℝ)/((((1:ℕ+):ℕ):ℝ) + prefixEval [1,2,1,3] lowerTau) = _
  have h : prefixEval ([1,2,1,3] : List ℕ+) lowerTau = 1/(1 + pS) := by
    show (1:ℝ)/((((1:ℕ+):ℕ):ℝ) + prefixEval [2,1,3] lowerTau) = _
    norm_num [pS]
  rw [h]; norm_num

lemma theta35_eq : lowerTheta 35 = 1/(2 + 1/(1 + pS)) := by
  show prefixEval [2,1,2,1,3] lowerTau = _
  show (1:ℝ)/((((2:ℕ+):ℕ):ℝ) + prefixEval [1,2,1,3] lowerTau) = _
  have h : prefixEval ([1,2,1,3] : List ℕ+) lowerTau = 1/(1 + pS) := by
    show (1:ℝ)/((((1:ℕ+):ℕ):ℝ) + prefixEval [2,1,3] lowerTau) = _
    norm_num [pS]
  rw [h]; norm_num

lemma theta63_bounds : (4409/10000 : ℝ) < lowerTheta 63 ∧ lowerTheta 63 < (4410/10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pL_bounds
  rw [theta63_eq]
  have hp : (0:ℝ) < 2 + pL := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

lemma theta70_bounds : (5759/10000 : ℝ) < lowerTheta 70 ∧ lowerTheta 70 < (5761/10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pS_bounds
  rw [theta70_eq]
  have hs : (0:ℝ) < 1 + pS := by linarith
  have hin : (7360/10000 : ℝ) < 1/(1+pS) ∧ 1/(1+pS) < (7362/10000 : ℝ) := by
    constructor
    · rw [lt_div_iff₀ hs]; linarith
    · rw [div_lt_iff₀ hs]; linarith
  have hd : (0:ℝ) < 1 + 1/(1+pS) := by linarith [hin.1]
  constructor
  · rw [lt_div_iff₀ hd]; linarith [hin.2]
  · rw [div_lt_iff₀ hd]; linarith [hin.1]

lemma theta35_bounds : (3654/10000 : ℝ) < lowerTheta 35 ∧ lowerTheta 35 < (3655/10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := pS_bounds
  rw [theta35_eq]
  have hs : (0:ℝ) < 1 + pS := by linarith
  have hin : (7360/10000 : ℝ) < 1/(1+pS) ∧ 1/(1+pS) < (7362/10000 : ℝ) := by
    constructor
    · rw [lt_div_iff₀ hs]; linarith
    · rw [div_lt_iff₀ hs]; linarith
  have hd : (0:ℝ) < 2 + 1/(1+pS) := by linarith [hin.1]
  constructor
  · rw [lt_div_iff₀ hd]; linarith [hin.2]
  · rw [div_lt_iff₀ hd]; linarith [hin.1]

/-! ### the single-variable polynomial inequalities behind the `lowerH p 5` exclusion -/

lemma polyq (r : ℝ) (h1 : 1/4 ≤ r) (h2 : r ≤ 4/5) :
    (70/100)*((2265/1000+1265/1000*r)*(2795/1000+1795/1000*r))*(5+r)^2
      ≤ (2263/1000*(5+r)+5*r)*(2789/1000*(5+r)+5*r) := by
  nlinarith [sq_nonneg (r - 1/4), sq_nonneg (r - 4/5), sq_nonneg r, h1, h2,
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)) (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)) (sub_nonneg.mpr h2)]

lemma polyt (r : ℝ) (h1 : 1/4 ≤ r) (h2 : r ≤ 4/5) :
    (558/1000)*((5+r)+(4410/10000)*(5*r))*((5+r)+(5761/10000)*(5*r))
      ≤ (65/100)*((1+3654/10000*r)*(1+4409/10000*r))*(5+r)^2 := by
  nlinarith [sq_nonneg (r - 1/4), sq_nonneg (r - 4/5), sq_nonneg r, h1, h2,
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)) (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)) (sub_nonneg.mpr h2)]

/-! ### the `lowerH p 5` exclusion of the reflection tie for the label `([1],[])`, `d = 2` -/

lemma h5_qlb (r1 r2 al be : ℝ)
    (hr1a : 1/4 ≤ r1) (hr1b : r1 ≤ 4/5) (hr2a : 0 ≤ r2)
    (hal : 263/1000 < al) (hah : al < 265/1000) (hbe : be = 3*al)
    (hrefl : r2*(5+r1) = 5*r1) :
    (70/100) * ((2+al+r1*(1+al))*(2+be+r1*(1+be))) ≤ (2+al+r2)*(2+be+r2) := by
  subst hbe
  have hr10 : (0:ℝ) ≤ r1 := by linarith
  have hsq : (0:ℝ) < (5+r1)^2 := by positivity
  have hm1 : al*(1+r1) ≤ 265/1000*(1+r1) :=
    mul_le_mul_of_nonneg_right hah.le (by linarith)
  have hNq : (2263/1000 + r2)*(2789/1000 + r2) ≤ (2+al+r2)*(2+3*al+r2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hDqub : (2+al+r1*(1+al))*(2+3*al+r1*(1+3*al))
      ≤ (2265/1000+1265/1000*r1)*(2795/1000+1795/1000*r1) :=
    mul_le_mul (by nlinarith [hm1]) (by nlinarith [hm1]) (by nlinarith) (by linarith)
  have hid : ((2263/1000 + r2)*(2789/1000 + r2)) * (5+r1)^2
      = (2263/1000*(5+r1)+5*r1)*(2789/1000*(5+r1)+5*r1) := by
    linear_combination ((2263/1000 + 2789/1000)*(5+r1) + r2*(5+r1) + 5*r1) * hrefl
  have h2q : (70/100)*((2265/1000+1265/1000*r1)*(2795/1000+1795/1000*r1))
      ≤ (2263/1000 + r2)*(2789/1000 + r2) := by
    apply le_of_mul_le_mul_right _ hsq
    rw [hid]
    linarith [polyq r1 hr1a hr1b]
  linarith [h2q, hNq, hDqub]

lemma h5_tub (r1 r2 t35 t63 t70 : ℝ)
    (hr1a : 1/4 ≤ r1) (hr1b : r1 ≤ 4/5) (hr2a : 0 ≤ r2)
    (h35 : 3654/10000 < t35) (h63 : 4409/10000 < t63)
    (h63' : t63 < 4410/10000) (h70' : t70 < 5761/10000) (h70a : 0 ≤ t70)
    (hrefl : r2*(5+r1) = 5*r1) :
    (279/500)*((1+r2*t63)*(1+r2*t70)) ≤ (65/100)*((1+r1*t35)*(1+r1*t63)) := by
  have hr10 : (0:ℝ) ≤ r1 := by linarith
  have hsq : (0:ℝ) < (5+r1)^2 := by positivity
  have hNt : (1+r2*t63)*(1+r2*t70) ≤ (1+4410/10000*r2)*(1+5761/10000*r2) :=
    mul_le_mul (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have hDtlb : (1+3654/10000*r1)*(1+4409/10000*r1) ≤ (1+r1*t35)*(1+r1*t63) :=
    mul_le_mul (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have hid2 : ((1+4410/10000*r2)*(1+5761/10000*r2)) * (5+r1)^2
      = ((5+r1)+(4410/10000)*(5*r1))*((5+r1)+(5761/10000)*(5*r1)) := by
    linear_combination ((5+r1)*(4410/10000 + 5761/10000)
      + (4410/10000)*(5761/10000)*(r2*(5+r1) + 5*r1)) * hrefl
  have h2t : (558/1000)*((1+4410/10000*r2)*(1+5761/10000*r2))
      ≤ (65/100)*((1+3654/10000*r1)*(1+4409/10000*r1)) := by
    apply le_of_mul_le_mul_right _ hsq
    rw [show (558/1000 : ℝ)*((1+4410/10000*r2)*(1+5761/10000*r2)) * (5+r1)^2
        = (558/1000)*(((1+4410/10000*r2)*(1+5761/10000*r2)) * (5+r1)^2) by ring, hid2]
    linarith [polyt r1 hr1a hr1b]
  linarith [h2t, hNt, hDtlb]

lemma h5_contra (r1 r2 al be qs t35 t63 t70 : ℝ)
    (hr1a : 1/4 ≤ r1) (hr1b : r1 ≤ 4/5) (hr2a : 0 ≤ r2)
    (hal : 263/1000 < al) (hah : al < 265/1000) (hbe : be = 3*al)
    (hrefl : r2*(5+r1) = 5*r1)
    (hq : qs * ((2+al+r1*(1+al))*(2+be+r1*(1+be))) = (2+al+r2)*(2+be+r2))
    (h35 : 3654/10000 < t35) (h63 : 4409/10000 < t63)
    (h63' : t63 < 4410/10000) (h70' : t70 < 5761/10000) (h70a : 0 ≤ t70)
    (hH5 : qs * ((1+r1*t35)*(1+r1*t63)) < (279/500)*((1+r2*t63)*(1+r2*t70))) : False := by
  have hr10 : (0:ℝ) ≤ r1 := by linarith
  have hal0 : (0:ℝ) < al := by linarith
  have hDq : (0:ℝ) < (2+al+r1*(1+al))*(2+be+r1*(1+be)) := by
    have e0 : (0:ℝ) ≤ r1*(1+al) := mul_nonneg hr10 (by linarith)
    have e1 : (0:ℝ) ≤ r1*(1+be) := mul_nonneg hr10 (by rw [hbe]; linarith)
    apply mul_pos <;> [linarith; (rw [hbe]; linarith)]
  have hDt : (0:ℝ) < (1+r1*t35)*(1+r1*t63) := by
    have e0 : (0:ℝ) ≤ r1*t35 := mul_nonneg hr10 (by linarith)
    have e1 : (0:ℝ) ≤ r1*t63 := mul_nonneg hr10 (by linarith)
    apply mul_pos <;> linarith
  have hqlb : (70/100:ℝ) ≤ qs := by
    apply le_of_mul_le_mul_right _ hDq
    linarith [hq, h5_qlb r1 r2 al be hr1a hr1b hr2a hal hah hbe hrefl]
  linarith [mul_le_mul_of_nonneg_right hqlb (le_of_lt hDt), hH5,
    h5_tub r1 r2 t35 t63 t70 hr1a hr1b hr2a h35 h63 h63' h70' h70a hrefl, hDt]

/-! ### from the raw geometry to `lowerGood` of a child -/

lemma inside_mem1 (ls : List LowerLabel) (l : LowerLabel) (hl : l ∈ ls) (wide tl : Bool) :
    (⟨lowerHistorySet (section14LabelWords l) wide
        (lowerHistoryPick (section14LabelWords l) wide ++ [1]), true,
      lowerHistorySet (section14LabelWords l) wide
        (lowerHistoryPick (section14LabelWords l) wide ++ [2]), false, true,
      [(⟨wide,wide,lowerHistoryWH (section14LabelWords l)⟩ : CertBound)]⟩ : Section14Spec)
      ∈ section14ExpectedSpecs ls tl := by
  simp only [section14ExpectedSpecs]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨l, hl, ?_⟩
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨(wide, ⟨wide,wide,lowerHistoryWH (section14LabelWords l)⟩), ?_, ?_⟩
  · cases wide <;> simp [section14NormalCases]
  · simp

lemma inside_mem2 (ls : List LowerLabel) (l : LowerLabel) (hl : l ∈ ls) (wide tl : Bool) :
    (⟨lowerHistorySet (section14LabelWords l) wide
        (lowerHistoryPick (section14LabelWords l) wide ++ [2]), true,
      lowerHistorySet (section14LabelWords l) wide
        (lowerHistoryPick (section14LabelWords l) wide ++ [1]), false, true,
      [(⟨wide,wide,lowerHistoryWH (section14LabelWords l)⟩ : CertBound)]⟩ : Section14Spec)
      ∈ section14ExpectedSpecs ls tl := by
  simp only [section14ExpectedSpecs]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨l, hl, ?_⟩
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨(wide, ⟨wide,wide,lowerHistoryWH (section14LabelWords l)⟩), ?_, ?_⟩
  · cases wide <;> simp [section14NormalCases]
  · simp

lemma label_good (p : LowerPair) (ls : List LowerLabel) (l : LowerLabel) (hl : l ∈ ls) (tl : Bool)
    (hg : ∀ s ∈ section14ExpectedSpecs ls tl, section14SpecHolds p s)
    (hsw1 : lowerCover ((lowerNormalize p).1 ++ (section14LabelWords l).1,
              ((lowerNormalize p).2 ++ (section14LabelWords l).2) ++ [1])
            ⊆ lowerCover (((lowerNormalize p).2 ++ (section14LabelWords l).2) ++ [1],
              (lowerNormalize p).1 ++ (section14LabelWords l).1))
    (hsw2 : lowerCover ((lowerNormalize p).1 ++ (section14LabelWords l).1,
              ((lowerNormalize p).2 ++ (section14LabelWords l).2) ++ [2])
            ⊆ lowerCover (((lowerNormalize p).2 ++ (section14LabelWords l).2) ++ [2],
              (lowerNormalize p).1 ++ (section14LabelWords l).1)) :
    lowerGood (lowerChild p l) := by
  classical
  have key : ∀ wide : Bool,
      certBoundHolds ⟨wide,wide,lowerHistoryWH (section14LabelWords l)⟩
          (section14R p) (section14S p) (section14Q p) →
      (lowerEndpoint ((lowerNormalize p).1 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [1])).1,
          (lowerNormalize p).2 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [1])).2) false
        < lowerEndpoint ((lowerNormalize p).1 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [2])).1,
          (lowerNormalize p).2 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [2])).2) true
       ∧ lowerEndpoint ((lowerNormalize p).1 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [2])).1,
          (lowerNormalize p).2 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [2])).2) false
        < lowerEndpoint ((lowerNormalize p).1 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [1])).1,
          (lowerNormalize p).2 ++
            (lowerHistorySet (section14LabelWords l) wide
              (lowerHistoryPick (section14LabelWords l) wide ++ [1])).2) true) := by
    intro wide hb
    have hh : section14Holds [(⟨wide,wide,lowerHistoryWH (section14LabelWords l)⟩ : CertBound)]
        (section14R p) (section14S p) (section14Q p) := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx; exact hb
    have s1 := hg _ (inside_mem1 ls l hl wide tl) hh
    have s2 := hg _ (inside_mem2 ls l hl wide tl) hh
    exact pair_overlap_of_specs p _ _ s1 s2
  have hcc : lowerChild p l
      = ((lowerNormalize p).1 ++ (section14LabelWords l).1,
         (lowerNormalize p).2 ++ (section14LabelWords l).2) := rfl
  rw [hcc]
  apply child_good_core
  · intro hle
    have hb : certBoundHolds (⟨false,false,lowerHistoryWH (section14LabelWords l)⟩ : CertBound)
        (section14R p) (section14S p) (section14Q p) := by
      show section14Q p ≤ certThresholdVal (lowerHistoryWH (section14LabelWords l))
        (section14R p) (section14S p)
      exact (wide_iff (lowerNormalize p) (section14LabelWords l)).mpr hle
    have h := key false hb
    simpa [lowerHistorySet, lowerHistoryPick, List.append_assoc] using h
  · intro hlt
    refine ⟨?_, hsw1, hsw2⟩
    have hb : certBoundHolds (⟨true,true,lowerHistoryWH (section14LabelWords l)⟩ : CertBound)
        (section14R p) (section14S p) (section14Q p) := by
      show certThresholdVal (lowerHistoryWH (section14LabelWords l))
        (section14R p) (section14S p) < section14Q p
      have h1 : ¬ (section14Q p ≤ certThresholdVal (lowerHistoryWH (section14LabelWords l))
          (section14R p) (section14S p)) := fun hcon =>
        absurd ((wide_iff (lowerNormalize p) (section14LabelWords l)).mp hcon) (not_le.mpr hlt)
      exact not_le.mp h1
    have h := key true hb
    simpa [lowerHistorySet, lowerHistoryPick, List.append_assoc] using h

/-! ### ruling out the reflection branch -/

lemma reflect_ratio (u v : List ℕ+)
    (h : 4*((lowerCD u).2 : ℤ)*((lowerCD v).2 : ℤ) =
        3*(((lowerCD u).1 : ℤ)*((lowerCD v).2 : ℤ) + ((lowerCD v).1 : ℤ)*((lowerCD u).2 : ℤ))
          + 4*((lowerCD u).1 : ℤ)*((lowerCD v).1 : ℤ)) :
    4 = 3*(lowerRatio u + lowerRatio v) + 4*(lowerRatio u * lowerRatio v) := by
  have hDu : (0:ℝ) < ((lowerCD u).2 : ℝ) := by exact_mod_cast cd_den_pos u
  have hDv : (0:ℝ) < ((lowerCD v).2 : ℝ) := by exact_mod_cast cd_den_pos v
  have hR : 4*((lowerCD u).2 : ℝ)*((lowerCD v).2 : ℝ) =
      3*(((lowerCD u).1 : ℝ)*((lowerCD v).2 : ℝ) + ((lowerCD v).1 : ℝ)*((lowerCD u).2 : ℝ))
        + 4*((lowerCD u).1 : ℝ)*((lowerCD v).1 : ℝ) := by exact_mod_cast h
  have e1 : lowerRatio u = ((lowerCD u).1 : ℝ)/((lowerCD u).2 : ℝ) := rfl
  have e2 : lowerRatio v = ((lowerCD v).1 : ℝ)/((lowerCD v).2 : ℝ) := rfl
  rw [e1, e2]
  field_simp
  linarith [hR]

lemma no_reflect_lb (u v : List ℕ+) (mu mv : ℝ)
    (hmu : 0 ≤ mu) (hmv : 0 ≤ mv)
    (hu : mu ≤ lowerRatio u) (hv : mv ≤ lowerRatio v)
    (hF : 4 < 3*(mu + mv) + 4*(mu*mv)) :
    ¬ (4 = 3*(lowerRatio u + lowerRatio v) + 4*(lowerRatio u * lowerRatio v)) := by
  intro h4
  have hpu := param_nonneg u
  have hprod : mu*mv ≤ lowerRatio u * lowerRatio v := mul_le_mul hu hv hmv hpu
  linarith

lemma no_reflect_ub (u v : List ℕ+) (Mu Mv : ℝ)
    (hu : lowerRatio u ≤ Mu) (hv : lowerRatio v ≤ Mv) (hMv : 0 ≤ Mv)
    (hF : 3*(Mu + Mv) + 4*(Mu*Mv) < 4) :
    ¬ (4 = 3*(lowerRatio u + lowerRatio v) + 4*(lowerRatio u * lowerRatio v)) := by
  intro h4
  have hpv := param_nonneg v
  have hMu : 0 ≤ Mu := le_trans (param_nonneg u) hu
  have hprod : lowerRatio u * lowerRatio v ≤ Mu*Mv := mul_le_mul hu hv hpv hMu
  linarith

lemma cd_le_of_no_reflect (u v : List ℕ+) (htie : lowerWidth u = lowerWidth v)
    (hno : ¬ (4 = 3*(lowerRatio u + lowerRatio v) + 4*(lowerRatio u * lowerRatio v))) :
    (lowerCD u).1 ≤ (lowerCD v).1 := by
  rcases tie_dichotomy u v htie with hcd | href
  · rw [hcd]
  · exact absurd (reflect_ratio u v href) hno

lemma width_ne_of_no_reflect (u v : List ℕ+)
    (hne : lowerRatio u ≠ lowerRatio v)
    (hno : ¬ (4 = 3*(lowerRatio u + lowerRatio v) + 4*(lowerRatio u * lowerRatio v))) :
    lowerWidth u ≠ lowerWidth v := by
  intro htie
  rcases tie_dichotomy u v htie with hcd | href
  · exact hne (by simp only [ratio_eq, rCD, hcd])
  · exact hno (reflect_ratio u v href)

lemma cd_le_tie_d1 (q2 u : List ℕ+) (hq2 : q2 ≠ [1])
    (htie : lowerWidth u = lowerWidth (q2 ++ [1])) :
    (lowerCD u).1 ≤ (lowerCD (q2 ++ [1])).1 := by
  apply cd_le_of_tie u (q2 ++ [1]) htie
  have hlt := cd_lt q2 hq2
  have hone : ((1:ℕ+):ℕ) = 1 := rfl
  rw [lowerCD_append, hone, one_mul]
  omega

lemma cover_swap_equal (a b : List ℕ+) (hpar : a.length % 2 = b.length % 2)
    (h : lowerWidth b ≠ lowerWidth a) : lowerCover (a,b) ⊆ lowerCover (b,a) := by
  intro t ht
  rw [lowerCover, Set.mem_Icc] at ht ⊢
  rw [← endpoint_swap_equalParity a b false hpar h, ← endpoint_swap_equalParity a b true hpar h]
  exact ht

/-! ### the deep tie of the `([1],[]) , d = 2` family pins the scale -/

lemma pe11 (x : ℝ) : prefixEval [1,1] x = 1/(1+1/(1+x)) := by
  show (1:ℝ)/((((1:ℕ+):ℕ):ℝ) + prefixEval [1] x) = _
  rw [pe_single]
  norm_num

lemma cd11 : (rCD [1,1]).2 = 2 ∧ lowerRatio [1,1] = 1/2 := by
  constructor
  · show (((lowerCD [1,1]).2 : ℕ) : ℝ) = 2
    norm_num [lowerCD]
  · show (((lowerCD [1,1]).1 : ℕ) : ℝ)/(((lowerCD [1,1]).2 : ℕ) : ℝ) = 1/2
    norm_num [lowerCD]

lemma width11 : lowerWidth [1,1] = (lowerBeta - lowerAlpha)/((2+lowerAlpha)*(2+lowerBeta)) := by
  rw [width_eq, cd11.1, cd11.2]; congr 1; ring

lemma widthA (w : List ℕ+) : lowerWidth (w ++ [1,1]) = (lowerBeta - lowerAlpha) /
    ((rCD w).2^2 * ((2+lowerAlpha+lowerRatio w*(1+lowerAlpha))
      *(2+lowerBeta+lowerRatio w*(1+lowerBeta)))) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hal0 : (0:ℝ) < lowerAlpha := by linarith [alpha_lo]
  have h1 : (0:ℝ) < 1 + lowerAlpha := by linarith
  have h2 : (0:ℝ) < 1 + lowerBeta := by linarith [hB.1]
  have h3 : (0:ℝ) < 2 + lowerAlpha := by linarith
  have h4 : (0:ℝ) < 2 + lowerBeta := by linarith [hB.1]
  rw [width_append, width11, pe11, pe11, div_div]
  congr 1
  field_simp
  try ring

lemma widthB (w : List ℕ+) : lowerWidth (w ++ [2]) = (lowerBeta - lowerAlpha) /
    ((rCD w).2^2 * ((2+lowerAlpha+lowerRatio w)*(2+lowerBeta+lowerRatio w))) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hal0 : (0:ℝ) < lowerAlpha := by linarith [alpha_lo]
  have h3 : (0:ℝ) < 2 + lowerAlpha := by linarith
  have h4 : (0:ℝ) < 2 + lowerBeta := by linarith [hB.1]
  have hc : (((2:ℕ+):ℕ):ℝ) = 2 := by norm_num
  rw [width_append, width_single, hc, pe_single, pe_single, hc, div_div]
  congr 1
  field_simp
  try ring

lemma tie_scale (q : LowerPair)
    (htie : lowerWidth ((q.1 ++ [1]) ++ [1]) = lowerWidth (q.2 ++ [2])) :
    lowerScale q * ((2+lowerAlpha+lowerRatio q.1*(1+lowerAlpha))
        *(2+lowerBeta+lowerRatio q.1*(1+lowerBeta)))
      = (2+lowerAlpha+lowerRatio q.2)*(2+lowerBeta+lowerRatio q.2) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hal0 : (0:ℝ) < lowerAlpha := by linarith [alpha_lo]
  have hba : (0:ℝ) < lowerBeta - lowerAlpha := sub_pos.mpr hab
  have hr1 := param_nonneg q.1
  have hr2 := param_nonneg q.2
  have hD1 : (0:ℝ) < (rCD q.1).2 := (cd_pos q.1).2
  have hD2 : (0:ℝ) < (rCD q.2).2 := (cd_pos q.2).2
  have hassoc : (q.1 ++ [1]) ++ [1] = q.1 ++ [1,1] := by simp
  rw [hassoc, widthA, widthB] at htie
  have hP1 : (0:ℝ) < (rCD q.1).2^2 * ((2+lowerAlpha+lowerRatio q.1*(1+lowerAlpha))
      *(2+lowerBeta+lowerRatio q.1*(1+lowerBeta))) := by
    apply mul_pos (by positivity)
    apply mul_pos <;> nlinarith [hB.1]
  have hP2 : (0:ℝ) < (rCD q.2).2^2 * ((2+lowerAlpha+lowerRatio q.2)*(2+lowerBeta+lowerRatio q.2)) := by
    apply mul_pos (by positivity)
    apply mul_pos <;> nlinarith [hB.1]
  rw [div_eq_div_iff (ne_of_gt hP1) (ne_of_gt hP2)] at htie
  have hkey : (rCD q.1).2^2 * ((2+lowerAlpha+lowerRatio q.1*(1+lowerAlpha))
      *(2+lowerBeta+lowerRatio q.1*(1+lowerBeta)))
      = (rCD q.2).2^2 * ((2+lowerAlpha+lowerRatio q.2)*(2+lowerBeta+lowerRatio q.2)) :=
    (mul_left_cancel₀ (ne_of_gt hba) htie).symm
  have hs : lowerScale q = (rCD q.1).2^2 / (rCD q.2).2^2 := rfl
  rw [hs]
  field_simp
  linarith [hkey]

lemma refl_curve (r1 r2 : ℝ) (h1 : 0 ≤ r1) (h2 : 0 ≤ r2)
    (h : 4 = 3*(1/(1+1/(1+r1)) + 1/(2+r2)) + 4*((1/(1+1/(1+r1)))*(1/(2+r2)))) :
    r2*(5+r1) = 5*r1 := by
  have d1 : (0:ℝ) < 1+r1 := by linarith
  have d2 : (0:ℝ) < 2+r2 := by linarith
  have e : 1/(1+1/(1+r1)) = (1+r1)/(2+r1) := by
    rw [eq_div_iff (by linarith)]
    field_simp
    ring
  rw [e] at h
  have d3 : (0:ℝ) < 2+r1 := by linarith
  field_simp at h
  linarith

/-- the `([1],[])`, `d = 2` reflection tie is excluded by `lowerH p 5`. -/
lemma no_reflect_11_2 (p : LowerPair)
    (hb1 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1)
    (hb2 : lowerRatio (lowerNormalize p).1 ≤ 4/5)
    (hH5 : lowerH p 5)
    (htie : lowerWidth (((lowerNormalize p).1 ++ [1]) ++ [1])
      = lowerWidth ((lowerNormalize p).2 ++ [2])) :
    ¬ (4 = 3*(lowerRatio (((lowerNormalize p).1 ++ [1]) ++ [1])
              + lowerRatio ((lowerNormalize p).2 ++ [2]))
        + 4*(lowerRatio (((lowerNormalize p).1 ++ [1]) ++ [1])
              * lowerRatio ((lowerNormalize p).2 ++ [2]))) := by
  intro href
  have hone : (((1:ℕ+):ℕ):ℝ) = 1 := by norm_num
  have htwo : (((2:ℕ+):ℕ):ℝ) = 2 := by norm_num
  have e1 : lowerRatio ((lowerNormalize p).1 ++ [1]) = 1/(1 + lowerRatio (lowerNormalize p).1) := by
    rw [ratio_snoc, hone]
  have e2 : lowerRatio (((lowerNormalize p).1 ++ [1]) ++ [1])
      = 1/(1 + 1/(1 + lowerRatio (lowerNormalize p).1)) := by
    rw [ratio_snoc, hone, e1]
  have e3 : lowerRatio ((lowerNormalize p).2 ++ [2]) = 1/(2 + lowerRatio (lowerNormalize p).2) := by
    rw [ratio_snoc, htwo]
  rw [e2, e3] at href
  have hcurve := refl_curve _ _ (param_nonneg (lowerNormalize p).1)
    (param_nonneg (lowerNormalize p).2) href
  have hq := tie_scale (lowerNormalize p) htie
  have h5 : lowerScale (lowerNormalize p) < lowerThreshold p (279/500) 35 63 63 70 := hH5
  have hr1 := param_nonneg (lowerNormalize p).1
  have t35 := theta35_bounds
  have t63 := theta63_bounds
  have t70 := theta70_bounds
  have hden : (0:ℝ) < (1 + lowerRatio (lowerNormalize p).1 * lowerTheta 35)
      * (1 + lowerRatio (lowerNormalize p).1 * lowerTheta 63) := by
    have p1 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 * lowerTheta 35 :=
      mul_nonneg hr1 (by linarith [t35.1])
    have p2 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 * lowerTheta 63 :=
      mul_nonneg hr1 (by linarith [t63.1])
    apply mul_pos <;> linarith
  have hthr : lowerThreshold p (279/500) 35 63 63 70
      = (279/500)*((1 + lowerRatio (lowerNormalize p).2 * lowerTheta 63)
        * (1 + lowerRatio (lowerNormalize p).2 * lowerTheta 70))
        / ((1 + lowerRatio (lowerNormalize p).1 * lowerTheta 35)
          * (1 + lowerRatio (lowerNormalize p).1 * lowerTheta 63)) := rfl
  rw [hthr] at h5
  have h5' := (lt_div_iff₀ hden).mp h5
  exact h5_contra _ _ lowerAlpha lowerBeta _ (lowerTheta 35) (lowerTheta 63) (lowerTheta 70)
    hb1 hb2 (param_nonneg (lowerNormalize p).2) alpha_lo alpha_hi beta_eq hcurve hq
    t35.1 t63.1 t63.2 t70.2 (by linarith [t70.1]) h5'

/-! ### ratio bounds and the per-label swap transports -/

lemma pn1 : (((1:ℕ+):ℕ):ℝ) = 1 := by norm_num
lemma pn2 : (((2:ℕ+):ℕ):ℝ) = 2 := by norm_num
lemma pn3 : (((3:ℕ+):ℕ):ℝ) = 3 := by norm_num

lemma ratio_lb (w : List ℕ+) (c : ℕ+) (hi m : ℝ) (hhi : lowerRatio w ≤ hi) (h0 : 0 ≤ m)
    (hm : m * (((c:ℕ):ℝ) + hi) ≤ 1) : m ≤ lowerRatio (w ++ [c]) := by
  have hcc : (0:ℝ) < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hr := param_nonneg w
  have hd : (0:ℝ) < ((c:ℕ):ℝ) + lowerRatio w := by linarith
  rw [ratio_snoc, le_div_iff₀ hd]
  nlinarith

lemma ratio_ub (w : List ℕ+) (c : ℕ+) (lo M : ℝ) (hlo : lo ≤ lowerRatio w)
    (hM : 1 ≤ M * (((c:ℕ):ℝ) + lo)) (hM0 : 0 ≤ M) : lowerRatio (w ++ [c]) ≤ M := by
  have hcc : (0:ℝ) < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hr := param_nonneg w
  have hd : (0:ℝ) < ((c:ℕ):ℝ) + lowerRatio w := by linarith
  rw [ratio_snoc, div_le_iff₀ hd]
  nlinarith

lemma hsw_plain (q : LowerPair) (x d : ℕ+)
    (hpar : ¬ (q.1.length % 2 = q.2.length % 2))
    (hq2 : q.2 ≠ [])
    (hgood : lowerWidth ((q.1 ++ [x]) ++ [1]) = lowerWidth (q.2 ++ [d]) →
       (lowerCD ((q.1 ++ [x]) ++ [1])).1 ≤ (lowerCD (q.2 ++ [d])).1) :
    lowerCover (q.1 ++ [x], q.2 ++ [d]) ⊆ lowerCover (q.2 ++ [d], q.1 ++ [x]) := by
  apply cover_swap_mixed
  · simp only [List.length_append, List.length_singleton]; omega
  · intro h
    apply hq2
    have hl := congrArg List.length h
    simp only [List.length_append, List.length_singleton, List.length_cons,
      List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  · exact hgood

lemma hsw_31 (q : LowerPair) (d : ℕ+)
    (hpar : ¬ (q.1.length % 2 = q.2.length % 2))
    (hne : lowerWidth ((q.2 ++ [1]) ++ [d]) ≠ lowerWidth (q.1 ++ [3])) :
    lowerCover (q.1 ++ [3], (q.2 ++ [1]) ++ [d])
      ⊆ lowerCover ((q.2 ++ [1]) ++ [d], q.1 ++ [3]) := by
  apply cover_swap_equal
  · simp only [List.length_append, List.length_singleton]; omega
  · exact hne

/-! ### the four label families -/

lemma good_d1 (q : LowerPair) (x : ℕ+) (hq2 : q.2 ≠ [1]) :
    lowerWidth ((q.1 ++ [x]) ++ [1]) = lowerWidth (q.2 ++ [1]) →
      (lowerCD ((q.1 ++ [x]) ++ [1])).1 ≤ (lowerCD (q.2 ++ [1])).1 :=
  fun htie => cd_le_tie_d1 q.2 _ hq2 htie

lemma good_22 (q : LowerPair)
    (hb1 : (1:ℝ)/4 ≤ lowerRatio q.1) (hb4 : lowerRatio q.2 ≤ 4/5) :
    lowerWidth ((q.1 ++ [2]) ++ [1]) = lowerWidth (q.2 ++ [2]) →
      (lowerCD ((q.1 ++ [2]) ++ [1])).1 ≤ (lowerCD (q.2 ++ [2])).1 := by
  intro htie
  apply cd_le_of_no_reflect _ _ htie
  have u1 : lowerRatio (q.1 ++ [2]) ≤ 4/9 :=
    ratio_ub q.1 2 (1/4) (4/9) hb1 (by rw [pn2]; norm_num) (by norm_num)
  have u2 : (9/13:ℝ) ≤ lowerRatio ((q.1 ++ [2]) ++ [1]) :=
    ratio_lb (q.1 ++ [2]) 1 (4/9) (9/13) u1 (by norm_num) (by rw [pn1]; norm_num)
  have v1 : (5/14:ℝ) ≤ lowerRatio (q.2 ++ [2]) :=
    ratio_lb q.2 2 (4/5) (5/14) hb4 (by norm_num) (by rw [pn2]; norm_num)
  exact no_reflect_lb _ _ (9/13) (5/14) (by norm_num) (by norm_num) u2 v1 (by norm_num)

lemma good_32 (q : LowerPair)
    (hb1 : (1:ℝ)/4 ≤ lowerRatio q.1) (hb4 : lowerRatio q.2 ≤ 4/5) :
    lowerWidth ((q.1 ++ [3]) ++ [1]) = lowerWidth (q.2 ++ [2]) →
      (lowerCD ((q.1 ++ [3]) ++ [1])).1 ≤ (lowerCD (q.2 ++ [2])).1 := by
  intro htie
  apply cd_le_of_no_reflect _ _ htie
  have u1 : lowerRatio (q.1 ++ [3]) ≤ 4/13 :=
    ratio_ub q.1 3 (1/4) (4/13) hb1 (by rw [pn3]; norm_num) (by norm_num)
  have u2 : (13/17:ℝ) ≤ lowerRatio ((q.1 ++ [3]) ++ [1]) :=
    ratio_lb (q.1 ++ [3]) 1 (4/13) (13/17) u1 (by norm_num) (by rw [pn1]; norm_num)
  have v1 : (5/14:ℝ) ≤ lowerRatio (q.2 ++ [2]) :=
    ratio_lb q.2 2 (4/5) (5/14) hb4 (by norm_num) (by rw [pn2]; norm_num)
  exact no_reflect_lb _ _ (13/17) (5/14) (by norm_num) (by norm_num) u2 v1 (by norm_num)

lemma good_12 (p : LowerPair)
    (hb1 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1)
    (hb2 : lowerRatio (lowerNormalize p).1 ≤ 4/5) (hH5 : lowerH p 5) :
    lowerWidth (((lowerNormalize p).1 ++ [1]) ++ [1])
        = lowerWidth ((lowerNormalize p).2 ++ [2]) →
      (lowerCD (((lowerNormalize p).1 ++ [1]) ++ [1])).1
        ≤ (lowerCD ((lowerNormalize p).2 ++ [2])).1 :=
  fun htie => cd_le_of_no_reflect _ _ htie (no_reflect_11_2 p hb1 hb2 hH5 htie)

lemma ne31_d (q : LowerPair) (d : ℕ+) (hd : d = 1 ∨ d = 2)
    (hb1 : (1:ℝ)/4 ≤ lowerRatio q.1)
    (hb3 : (1:ℝ)/4 ≤ lowerRatio q.2) (hb4 : lowerRatio q.2 ≤ 4/5) :
    lowerWidth ((q.2 ++ [1]) ++ [d]) ≠ lowerWidth (q.1 ++ [3]) := by
  have w1 : (5/9:ℝ) ≤ lowerRatio (q.2 ++ [1]) :=
    ratio_lb q.2 1 (4/5) (5/9) hb4 (by norm_num) (by rw [pn1]; norm_num)
  have w2 : lowerRatio (q.2 ++ [1]) ≤ 4/5 :=
    ratio_ub q.2 1 (1/4) (4/5) hb3 (by rw [pn1]; norm_num) (by norm_num)
  have v2 : lowerRatio (q.1 ++ [3]) ≤ 4/13 :=
    ratio_ub q.1 3 (1/4) (4/13) hb1 (by rw [pn3]; norm_num) (by norm_num)
  rcases hd with rfl | rfl
  · have u1 : (5/9:ℝ) ≤ lowerRatio ((q.2 ++ [1]) ++ [1]) :=
      ratio_lb (q.2 ++ [1]) 1 (4/5) (5/9) w2 (by norm_num) (by rw [pn1]; norm_num)
    have u2 : lowerRatio ((q.2 ++ [1]) ++ [1]) ≤ 9/14 :=
      ratio_ub (q.2 ++ [1]) 1 (5/9) (9/14) w1 (by rw [pn1]; norm_num) (by norm_num)
    refine width_ne_of_no_reflect _ _ (fun hcon => ?_)
      (no_reflect_ub _ _ (9/14) (4/13) u2 v2 (by norm_num) (by norm_num))
    rw [hcon] at u1; linarith
  · have u1 : (5/14:ℝ) ≤ lowerRatio ((q.2 ++ [1]) ++ [2]) :=
      ratio_lb (q.2 ++ [1]) 2 (4/5) (5/14) w2 (by norm_num) (by rw [pn2]; norm_num)
    have u2 : lowerRatio ((q.2 ++ [1]) ++ [2]) ≤ 9/23 :=
      ratio_ub (q.2 ++ [1]) 2 (5/9) (9/23) w1 (by rw [pn2]; norm_num) (by norm_num)
    refine width_ne_of_no_reflect _ _ (fun hcon => ?_)
      (no_reflect_ub _ _ (9/23) (4/13) u2 v2 (by norm_num) (by norm_num))
    rw [hcon] at u1; linarith

/-! ### the covering walk and the parent anchor -/

lemma adm_words (p : LowerPair) (hadm : lowerAdmissible p) :
    p.1 ≠ [] ∧ p.1 ≠ [1] ∧ p.2 ≠ [] ∧ p.2 ≠ [1] := by
  obtain ⟨⟨c, hcmem, u, v, heq, _, _⟩, _⟩ := hadm
  have h1 : p.1 = c.1 ++ u := congrArg Prod.fst heq
  have h2 : p.2 = c.2 ++ v := congrArg Prod.snd heq
  fin_cases hcmem <;> rw [h1, h2] <;>
    exact ⟨by simp, by simp, by simp, by simp⟩

noncomputable def locUp (p : LowerPair) (l : LowerLabel) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint (lowerChild p l) true
  else -lowerEndpoint (lowerChild p l) false

lemma spec_low (p : LowerPair) (l : LowerLabel) :
    section14LocalEndpoint p (section14LabelWords l) false = lowerLocalLower p l := rfl
lemma spec_up (p : LowerPair) (l : LowerLabel) :
    section14LocalEndpoint p (section14LabelWords l) true = locUp p l := rfl

lemma local_membership (p : LowerPair) (l : LowerLabel) (t : ℝ) :
    t ∈ lowerCover (lowerChild p l) ↔
      lowerLocalLower p l ≤ lowerLocalCoordinate p t ∧
      lowerLocalCoordinate p t ≤ locUp p l := by
  unfold lowerCover lowerLocalLower lowerLocalCoordinate locUp
  split_ifs <;> simp only [Set.mem_Icc, neg_le_neg_iff]
  exact and_comm

lemma spec_weak (p : LowerPair) (a b : LowerPair) (ua ub : Bool)
    (h : section14SpecHolds p ⟨a,ua,b,ub,false,[]⟩) :
    section14LocalEndpoint p b ub ≤ section14LocalEndpoint p a ua := by
  simpa using h (by intro c hc; simp at hc)

lemma select3 (t : ℝ) (p : LowerPair) (l₁ l₂ l₃ : LowerLabel)
    (hls : section14RawList p = [l₁,l₂,l₃])
    (htl : section14TargetLower p = false)
    (hg : section14RawGeometry p)
    (hanchorLo : section14LocalEndpoint p ([],[]) false ≤ lowerLocalCoordinate p t)
    (hanchorHi : lowerLocalCoordinate p t ≤ section14LocalEndpoint p ([],[]) true)
    (hgood : ∀ l ∈ [l₁,l₂,l₃], lowerGood (lowerChild p l)) :
    ∃ l ∈ [l₁,l₂,l₃], lowerGood (lowerChild p l) ∧ t ∈ lowerCover (lowerChild p l) := by
  classical
  rw [section14RawGeometry, hls, htl] at hg
  have mem : ∀ s ∈ section14ExpectedSpecs [l₁,l₂,l₃] false, section14SpecHolds p s := hg
  have hhead : section14LocalEndpoint p ([],[]) true ≤ locUp p l₁ := by
    have := spec_weak p (section14LabelWords l₁) ([],[]) true true
      (mem _ (by simp [section14ExpectedSpecs]))
    simpa [spec_up] using this
  have htail : lowerLocalLower p l₃ ≤ section14LocalEndpoint p ([],[]) false := by
    have := spec_weak p ([],[]) (section14LabelWords l₃) false false
      (mem _ (by simp [section14ExpectedSpecs]))
    simpa [spec_low] using this
  have hc21 : lowerLocalLower p l₁ ≤ locUp p l₂ := by
    have := spec_weak p (section14LabelWords l₂) (section14LabelWords l₁) true false
      (mem _ (by simp [section14ExpectedSpecs]))
    simpa [spec_low, spec_up] using this
  have hc32 : lowerLocalLower p l₂ ≤ locUp p l₃ := by
    have := spec_weak p (section14LabelWords l₃) (section14LabelWords l₂) true false
      (mem _ (by simp [section14ExpectedSpecs]))
    simpa [spec_low, spec_up] using this
  set x := lowerLocalCoordinate p t with hx
  by_cases h3 : x ≤ locUp p l₃
  · exact ⟨l₃, by simp, hgood _ (by simp),
      (local_membership p l₃ t).mpr ⟨le_trans htail hanchorLo, h3⟩⟩
  · by_cases h2 : x ≤ locUp p l₂
    · exact ⟨l₂, by simp, hgood _ (by simp),
        (local_membership p l₂ t).mpr ⟨le_trans hc32 (le_of_lt (lt_of_not_ge h3)), h2⟩⟩
    · exact ⟨l₁, by simp, hgood _ (by simp),
        (local_membership p l₁ t).mpr
          ⟨le_trans hc21 (le_of_lt (lt_of_not_ge h2)), le_trans hanchorHi hhead⟩⟩

lemma anchor_of_subset (t : ℝ) (p : LowerPair) (ht : t ∈ lowerCover p)
    (hsub : lowerCover p ⊆ lowerCover (lowerNormalize p)) :
    section14LocalEndpoint p ([],[]) false ≤ lowerLocalCoordinate p t ∧
      lowerLocalCoordinate p t ≤ section14LocalEndpoint p ([],[]) true := by
  classical
  have h := hsub ht
  rw [lowerCover, Set.mem_Icc] at h
  have hw : ((lowerNormalize p).1 ++ ([] : List ℕ+), (lowerNormalize p).2 ++ ([] : List ℕ+))
      = lowerNormalize p := by simp
  unfold section14LocalEndpoint lowerLocalCoordinate
  simp only [hw]
  split_ifs <;> constructor <;> simp_all <;> linarith [h.1, h.2]

lemma main_row (t : ℝ) (p : LowerPair) (l₃ : LowerLabel)
    (hls : section14RawList p = [([1],[]), ([2],[]), l₃])
    (htl : section14TargetLower p = false)
    (hg : section14RawGeometry p)
    (hml : lowerMixedList p = [([1],[]), ([2],[]), l₃])
    (hm : lowerMixed p) (htc : t ∈ lowerCover p) (hp2 : p.2 ≠ [1])
    (hgood : ∀ l ∈ [(([1],[]) : LowerLabel), ([2],[]), l₃], lowerGood (lowerChild p l)) :
    lowerNumericSuccessor t p := by
  classical
  have hsub := cover_subset_normalize p hm hp2
  obtain ⟨ha1, ha2⟩ := anchor_of_subset t p htc hsub
  obtain ⟨l, hl, hgl, hcl⟩ := select3 t p ([1],[]) ([2],[]) l₃ hls htl hg ha1 ha2 hgood
  refine Or.inr ⟨l, ?_, hgl, hcl⟩
  unfold lowerOffered
  left
  rw [if_pos hm, hml]
  exact hl

/-! ### goodness of the three children of the row -/

lemma good_label1 (p : LowerPair) (ls : List LowerLabel) (hl : (([1],[]) : LowerLabel) ∈ ls)
    (tl : Bool) (hg : ∀ s ∈ section14ExpectedSpecs ls tl, section14SpecHolds p s)
    (hpar : ¬ ((lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2))
    (hq2 : (lowerNormalize p).2 ≠ []) (hq2' : (lowerNormalize p).2 ≠ [1])
    (hb1 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1)
    (hb2 : lowerRatio (lowerNormalize p).1 ≤ 4/5) (hH5 : lowerH p 5) :
    lowerGood (lowerChild p ([1],[])) := by
  apply label_good p ls ([1],[]) hl tl hg
  · simpa [section14LabelWords] using
      hsw_plain (lowerNormalize p) 1 1 hpar hq2 (good_d1 (lowerNormalize p) 1 hq2')
  · simpa [section14LabelWords] using
      hsw_plain (lowerNormalize p) 1 2 hpar hq2 (good_12 p hb1 hb2 hH5)

lemma good_label2 (p : LowerPair) (ls : List LowerLabel) (hl : (([2],[]) : LowerLabel) ∈ ls)
    (tl : Bool) (hg : ∀ s ∈ section14ExpectedSpecs ls tl, section14SpecHolds p s)
    (hpar : ¬ ((lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2))
    (hq2 : (lowerNormalize p).2 ≠ []) (hq2' : (lowerNormalize p).2 ≠ [1])
    (hb1 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1)
    (hb4 : lowerRatio (lowerNormalize p).2 ≤ 4/5) :
    lowerGood (lowerChild p ([2],[])) := by
  apply label_good p ls ([2],[]) hl tl hg
  · simpa [section14LabelWords] using
      hsw_plain (lowerNormalize p) 2 1 hpar hq2 (good_d1 (lowerNormalize p) 2 hq2')
  · simpa [section14LabelWords] using
      hsw_plain (lowerNormalize p) 2 2 hpar hq2 (good_22 (lowerNormalize p) hb1 hb4)

lemma good_label3 (p : LowerPair) (ls : List LowerLabel) (hl : (([3],[]) : LowerLabel) ∈ ls)
    (tl : Bool) (hg : ∀ s ∈ section14ExpectedSpecs ls tl, section14SpecHolds p s)
    (hpar : ¬ ((lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2))
    (hq2 : (lowerNormalize p).2 ≠ []) (hq2' : (lowerNormalize p).2 ≠ [1])
    (hb1 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1)
    (hb4 : lowerRatio (lowerNormalize p).2 ≤ 4/5) :
    lowerGood (lowerChild p ([3],[])) := by
  apply label_good p ls ([3],[]) hl tl hg
  · simpa [section14LabelWords] using
      hsw_plain (lowerNormalize p) 3 1 hpar hq2 (good_d1 (lowerNormalize p) 3 hq2')
  · simpa [section14LabelWords] using
      hsw_plain (lowerNormalize p) 3 2 hpar hq2 (good_32 (lowerNormalize p) hb1 hb4)

lemma good_label31 (p : LowerPair) (ls : List LowerLabel) (hl : (([3],[1]) : LowerLabel) ∈ ls)
    (tl : Bool) (hg : ∀ s ∈ section14ExpectedSpecs ls tl, section14SpecHolds p s)
    (hpar : ¬ ((lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2))
    (hb1 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1)
    (hb3 : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).2)
    (hb4 : lowerRatio (lowerNormalize p).2 ≤ 4/5) :
    lowerGood (lowerChild p ([3],[1])) := by
  apply label_good p ls ([3],[1]) hl tl hg
  · simpa [section14LabelWords] using
      hsw_31 (lowerNormalize p) 1 hpar (ne31_d (lowerNormalize p) 1 (Or.inl rfl) hb1 hb3 hb4)
  · simpa [section14LabelWords] using
      hsw_31 (lowerNormalize p) 2 hpar (ne31_d (lowerNormalize p) 2 (Or.inr rfl) hb1 hb3 hb4)

end S14Tie

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : lowerMixed p ∧ ¬ lowerH p 2 ∧ lowerH p 5 ∧ ¬ lowerL p) (hg : section14RawGeometry p) :
    lowerNumericSuccessor t p := by
  classical
  obtain ⟨hm, hH2, hH5, hLL⟩ := hc
  obtain ⟨hadm, hgp, htc, hbox⟩ := hs
  obtain ⟨hw1, hw1', hw2, hw2'⟩ := S14Tie.adm_words p hadm
  have hnorm : lowerNormalize p = p ∨ lowerNormalize p = (p.2, p.1) := by
    unfold lowerNormalize
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hq2 : (lowerNormalize p).2 ≠ [] ∧ (lowerNormalize p).2 ≠ [1] := by
    rcases hnorm with h | h
    · rw [h]; exact ⟨hw2, hw2'⟩
    · rw [h]; exact ⟨hw1, hw1'⟩
  have hbx : (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).1 ∧
      lowerRatio (lowerNormalize p).1 ≤ 4/5 ∧
      (1:ℝ)/4 ≤ lowerRatio (lowerNormalize p).2 ∧
      lowerRatio (lowerNormalize p).2 ≤ 4/5 := by
    obtain ⟨b1, b2, b3, b4⟩ := hbox
    rcases hnorm with h | h
    · rw [h]; exact ⟨b1, b2, b3, b4⟩
    · rw [h]; exact ⟨b3, b4, b1, b2⟩
  have hpar : ¬ ((lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2) := by
    rcases hnorm with h | h
    · rw [h]; exact hm
    · rw [h]; exact fun hcon => hm hcon.symm
  have htl : section14TargetLower p = false := by unfold section14TargetLower; simp [hLL]
  have hml : lowerMixedList p = section14RawList p := by
    unfold lowerMixedList section14RawList
    simp only [if_neg hH2, if_pos hH5, if_neg hLL]
  by_cases h67 : lowerH p 6 ∧ lowerH p 7
  · have hls : section14RawList p = [([1],[]), ([2],[]), (([3],[]) : LowerLabel)] := by
      unfold section14RawList
      simp only [if_neg hH2, if_pos hH5, if_neg hLL, if_pos h67]
    have hg' : ∀ s ∈ section14ExpectedSpecs
        [(([1],[]) : LowerLabel), ([2],[]), ([3],[])] (section14TargetLower p),
        section14SpecHolds p s := by rw [← hls]; exact hg
    refine S14Tie.main_row t p ([3],[]) hls htl hg (by rw [hml, hls]) hm htc hw2' ?_
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact S14Tie.good_label1 p _ (by simp) _ hg' hpar hq2.1 hq2.2 hbx.1 hbx.2.1 hH5
    · exact S14Tie.good_label2 p _ (by simp) _ hg' hpar hq2.1 hq2.2 hbx.1 hbx.2.2.2
    · exact S14Tie.good_label3 p _ (by simp) _ hg' hpar hq2.1 hq2.2 hbx.1 hbx.2.2.2
  · have hls : section14RawList p = [([1],[]), ([2],[]), (([3],[1]) : LowerLabel)] := by
      unfold section14RawList
      simp only [if_neg hH2, if_pos hH5, if_neg hLL, if_neg h67]
    have hg' : ∀ s ∈ section14ExpectedSpecs
        [(([1],[]) : LowerLabel), ([2],[]), ([3],[1])] (section14TargetLower p),
        section14SpecHolds p s := by rw [← hls]; exact hg
    refine S14Tie.main_row t p ([3],[1]) hls htl hg (by rw [hml, hls]) hm htc hw2' ?_
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact S14Tie.good_label1 p _ (by simp) _ hg' hpar hq2.1 hq2.2 hbx.1 hbx.2.1 hH5
    · exact S14Tie.good_label2 p _ (by simp) _ hg' hpar hq2.1 hq2.2 hbx.1 hbx.2.2.2
    · exact S14Tie.good_label31 p _ (by simp) _ hg' hpar hbx.1 hbx.2.2.1 hbx.2.2.2

