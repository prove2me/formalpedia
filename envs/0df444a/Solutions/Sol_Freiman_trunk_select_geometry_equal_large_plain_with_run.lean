-- Prove2me | solution 1 for Freiman.trunk_select_geometry_equal_large_plain_with_run
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T19:35:16.882102+00:00
-- url     : https://prove2.me/submissions/94f92a40-34fa-403c-86be-ec7e8bfaa294

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Basic
import Mathlib.Topology.Connected.Basic

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

open Freiman

namespace LowerDev

set_option linter.unusedSimpArgs false

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

lemma scale_eq' (P : LowerPair) : lowerScale P = (rCD P.1).2 ^ 2 / (rCD P.2).2 ^ 2 := rfl

/-- Walking down a chain of overlapping intervals. -/
lemma walk {α : Type*} (lo hi : α → ℝ) (Rel : α → α → Prop)
    (hR : ∀ a b, Rel a b → lo a ≤ hi b) (x : ℝ) :
    ∀ (L : List α), L ≠ [] → List.IsChain Rel L →
      (∀ a, L.head? = some a → x ≤ hi a) →
      (∀ a, L.getLast? = some a → lo a ≤ x) →
      ∃ a ∈ L, lo a ≤ x ∧ x ≤ hi a
  | [], h, _, _, _ => absurd rfl h
  | [a], _, _, hh, hl => ⟨a, by simp, hl a (by simp), hh a (by simp)⟩
  | a :: b :: t, _, hchain, hh, hl => by
      by_cases hx : lo a ≤ x
      · exact ⟨a, by simp, hx, hh a (by simp)⟩
      · have hab : Rel a b := (List.isChain_cons_cons.mp hchain).1
        have hxb : x ≤ hi b := le_trans (le_of_lt (not_le.mp hx)) (hR a b hab)
        obtain ⟨c, hc, h1, h2⟩ :=
          walk lo hi Rel hR x (b :: t) (by simp) (List.isChain_cons_cons.mp hchain).2
            (fun a' ha' => by simp only [List.head?_cons, Option.some.injEq] at ha'; exact ha' ▸ hxb)
            (fun a' ha' => hl a' (by rw [List.getLast?_cons_cons]; exact ha'))
        exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩

end LowerDev

theorem solution (hJ : ∀ (t : ℝ) (p : LowerPair), lowerState t p → lowerRunOffered p → lowerRunFamily p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ ¬ lowerL p)
    (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  classical
  obtain ⟨hadm, hgoodp, hcov, hbox⟩ := hs
  obtain ⟨k, hfit, _hrect, hgeom⟩ := hg
  have hLf : ¬ ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.1 :=
    fun h => hc.2.2.2 (hfit.1.2.2.mpr h)
  -- ==== certificate-field dictionary ====
  have v3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3 := LowerDev.cf_tau [3]
  have v25 : certFieldVal (lowerHistoryTheta 25) = lowerTheta 25 := LowerDev.cf_tau [3,3]
  have v63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63 := LowerDev.cf_tau [2,3]
  have v66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66 := LowerDev.cf_tau [1,1,3]
  have v28 : certFieldVal (lowerHistoryTheta 28) = lowerTheta 28 := LowerDev.cf_alpha [3]
  have v65 : certFieldVal (lowerHistoryTheta 65) = lowerTheta 65 := LowerDev.cf_beta [1]
  have v1 : certFieldVal lowerHistoryAlpha = lowerTheta 1 := LowerDev.val_alpha
  have v95 : certFieldVal lowerHistoryBeta = lowerTheta 95 := LowerDev.val_beta
  have v36 : certFieldVal (lowerHistoryTheta 36) = lowerTheta 36 := by
    show certFieldVal (certFieldScale (1/2) lowerHistoryTau) = lowerTau / 2
    rw [LowerDev.val_scale, LowerDev.val_tau]; push_cast; ring
  have vc9 : certFieldVal (⟨3/2,-1/2,0,0⟩ : CertField) = (3 - Real.sqrt 3)/2 := by
    simp [certFieldVal]; push_cast; ring
  have vc20 : certFieldVal (⟨-171/255,0,0,76/255⟩ : CertField)
      = (-171 + 76*Real.sqrt 21)/255 := by
    simp [certFieldVal]; push_cast; ring
  -- ==== the cuts ====
  have hH7 : certBoundHolds lowerHistoryH7 (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
    show certThresholdVal (lowerHistoryThreshold (lowerHistoryRat (31/100))
      (lowerHistoryTheta 3, lowerHistoryTheta 25) (lowerHistoryTheta 63, lowerHistoryTheta 66))
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      ≤ lowerScale (lowerNormalize p)
    rw [LowerDev.threshold_value, LowerDev.val_rat, v3, v25, v63, v66]
    refine le_trans (le_of_eq ?_) (not_lt.mp hc.2.1)
    simp only [lowerThreshold] <;> push_cast <;> ring
  have hH9c : certBoundHolds (lowerHistoryComplement lowerHistoryH9)
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
    rw [LowerDev.complement_holds]
    refine not_le.mpr ?_
    show certThresholdVal (lowerHistoryThreshold (⟨3/2,-1/2,0,0⟩ : CertField)
      (lowerHistoryTheta 36, lowerHistoryTheta 63) (lowerHistoryTheta 63, lowerHistoryTheta 66))
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      < lowerScale (lowerNormalize p)
    rw [LowerDev.threshold_value, vc9, v36, v63, v66]
    refine lt_of_le_of_lt (le_of_eq ?_) (not_le.mp hc.2.2.1)
    simp only [lowerThreshold] <;> push_cast <;> ring
  have hH20eq : certThresholdVal (lowerHistoryThreshold (⟨-171/255,0,0,76/255⟩ : CertField)
      (lowerHistoryAlpha, lowerHistoryTheta 28) (lowerHistoryTheta 65, lowerHistoryBeta))
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      = lowerThreshold p ((-171+76*Real.sqrt 21)/255) 1 65 28 95 := by
    rw [LowerDev.threshold_value, vc20, v1, v28, v65, v95]
    simp only [lowerThreshold] <;> push_cast <;> ring
  have hH20 : lowerA p 20 → certBoundHolds trunkH20 (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
    intro h
    show lowerScale (lowerNormalize p) < certThresholdVal (lowerHistoryThreshold
      (⟨-171/255,0,0,76/255⟩ : CertField) (lowerHistoryAlpha, lowerHistoryTheta 28)
      (lowerHistoryTheta 65, lowerHistoryBeta)) (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2)
    rw [hH20eq]; exact h
  have hH20c : ¬ lowerA p 20 → certBoundHolds (lowerHistoryComplement trunkH20)
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
    intro h
    rw [LowerDev.complement_holds]
    show ¬ (lowerScale (lowerNormalize p) < certThresholdVal (lowerHistoryThreshold
      (⟨-171/255,0,0,76/255⟩ : CertField) (lowerHistoryAlpha, lowerHistoryTheta 28)
      (lowerHistoryTheta 65, lowerHistoryBeta)) (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2))
    rw [hH20eq]; exact h
  -- ==== local-coordinate dictionary ====
  have hF1 : ∀ l : LowerLabel, lowerLocalLower p l ≤ lowerLocalCoordinate p t →
      lowerLocalCoordinate p t ≤ trunkLocalUpper p l → t ∈ lowerCover (lowerChild p l) := by
    intro l ha hb'
    simp only [lowerLocalLower, trunkLocalUpper, lowerLocalCoordinate] at ha hb'
    show t ∈ Set.Icc _ _
    rw [Set.mem_Icc]
    by_cases hev : (lowerNormalize p).1.length % 2 = 0
    · simp only [hev, if_true] at ha hb'
      exact ⟨ha, hb'⟩
    · simp only [hev, if_false] at ha hb'
      constructor <;> linarith
  have hF2 : trunkParentEndpoint p false ≤ lowerLocalCoordinate p t ∧
      lowerLocalCoordinate p t ≤ trunkParentEndpoint p true := by
    have hcov' : lowerEndpoint p false ≤ t ∧ t ≤ lowerEndpoint p true := by
      have : t ∈ Set.Icc (lowerEndpoint p false) (lowerEndpoint p true) := hcov
      exact Set.mem_Icc.mp this
    simp only [trunkParentEndpoint, lowerLocalCoordinate]
    by_cases hev : (lowerNormalize p).1.length % 2 = 0
    · simp only [hev, if_true]
      exact ⟨hcov'.1, hcov'.2⟩
    · simp only [hev, if_false, Bool.not_false, Bool.not_true]
      constructor <;> linarith [hcov'.1, hcov'.2]
  have hF4 : ∀ l m : LowerLabel,
      (lowerCover (lowerChild p l) ∩ lowerCover (lowerChild p m)).Nonempty →
      lowerLocalLower p l ≤ trunkLocalUpper p m := by
    intro l m ⟨y, hy1, hy2⟩
    have h1' := Set.mem_Icc.mp hy1
    have h2' := Set.mem_Icc.mp hy2
    simp only [lowerLocalLower, trunkLocalUpper]
    by_cases hev : (lowerNormalize p).1.length % 2 = 0
    · simp only [hev, if_true]; linarith [h1'.1, h2'.2]
    · simp only [hev, if_false]; linarith [h1'.2, h2'.1]
  have sg : ∀ q : LowerPair, lowerStrictGood q → lowerGood q := by
    intro q h
    exact ⟨max (lowerEndpoint (lowerChild q ([1],[])) false)
               (lowerEndpoint (lowerChild q ([2],[])) false),
      ⟨le_max_left _ _, le_of_lt (lt_of_lt_of_le h (min_le_left _ _))⟩,
      ⟨le_max_right _ _, le_of_lt (lt_of_lt_of_le h (min_le_right _ _))⟩⟩
  have finish : ∀ (M : List LowerLabel), M ≠ [] →
      List.IsChain (fun l m => (lowerCover (lowerChild p l) ∩
        lowerCover (lowerChild p m)).Nonempty) ((([1],[]) : LowerLabel) :: M) →
      (∀ a ∈ (([1],[]) : LowerLabel) :: M,
        lowerOffered p a ∧ lowerGood (lowerChild p a)) →
      (lowerLocalCoordinate p t ≤ trunkLocalUpper p ([1],[])) →
      (∀ a, M.getLast? = some a → lowerLocalLower p a ≤ lowerLocalCoordinate p t) →
      lowerNumericSuccessor t p := by
    intro M hM hchain' hall hup hlast
    obtain ⟨b0, t0, rfl⟩ : ∃ b0 t0, M = b0 :: t0 := by
      cases M with
      | nil => exact absurd rfl hM
      | cons b0 t0 => exact ⟨b0, t0, rfl⟩
    obtain ⟨a, ha, h1, h2⟩ := LowerDev.walk (lowerLocalLower p) (trunkLocalUpper p) _
      hF4 (lowerLocalCoordinate p t) ((([1],[]) : LowerLabel) :: b0 :: t0) (by simp) hchain'
      (fun a' ha' => by
        simp only [List.head?_cons, Option.some.injEq] at ha'
        exact ha' ▸ hup)
      (fun a' ha' => hlast a' (by rwa [List.getLast?_cons_cons] at ha'))
    exact Or.inr ⟨a, (hall a ha).1, (hall a ha).2, hF1 a h1 h2⟩
  have hROof : ¬ lowerR p → ¬ certBoundHolds trunkShorten (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) → lowerRunOffered p := by
    intro hR hsh
    have hW : 0 < lowerWidth [3] := LowerDev.width_pos [3]
    have hXY : (0:ℝ) ≤ prefixEval [3] lowerAlpha ∧ (0:ℝ) ≤ prefixEval [3] lowerBeta :=
      ⟨(LowerDev.pe_unit [3] _ LowerDev.ab_unit.1).1,
       (LowerDev.pe_unit [3] _ LowerDev.ab_unit.2.1).1⟩
    have hr1n : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 := LowerDev.param_nonneg _
    have hr2n : (0:ℝ) ≤ lowerRatio (lowerNormalize p).2 := LowerDev.param_nonneg _
    have hD1 : (0:ℝ) < (LowerDev.rCD (lowerNormalize p).1).2 := (LowerDev.cd_pos _).2
    have hD2 : (0:ℝ) < (LowerDev.rCD (lowerNormalize p).2).2 := (LowerDev.cd_pos _).2
    have hP1 : (0:ℝ) < (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) *
        (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta) := by
      have h1 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha :=
        mul_nonneg hr1n hXY.1
      have h2 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta :=
        mul_nonneg hr1n hXY.2
      positivity
    have hP2 : (0:ℝ) < (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) *
        (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta) := by
      have h1 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha :=
        mul_nonneg hr2n hXY.1
      have h2 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta :=
        mul_nonneg hr2n hXY.2
      positivity
    have hB1 : (0:ℝ) < (LowerDev.rCD (lowerNormalize p).1).2 ^ 2 * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta) := by
      have h1 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha := mul_nonneg hr1n hXY.1
      have h2 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta := mul_nonneg hr1n hXY.2
      have h3 := hD1
      positivity
    have hB2 : (0:ℝ) < (LowerDev.rCD (lowerNormalize p).2).2 ^ 2 * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta) := by
      have h1 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha := mul_nonneg hr2n hXY.1
      have h2 : (0:ℝ) ≤ lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta := mul_nonneg hr2n hXY.2
      have h3 := hD2
      positivity
    have hP1n : (((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta)) : ℝ) ≠ 0 := ne_of_gt hP1
    have hD2sq : (0:ℝ) < ((LowerDev.rCD (lowerNormalize p).2).2 : ℝ) ^ 2 := by positivity
    have hkey : (7/5 : ℝ) * (((LowerDev.rCD (lowerNormalize p).1).2 : ℝ) ^ 2 * ((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta))) < ((LowerDev.rCD (lowerNormalize p).2).2 : ℝ) ^ 2 * ((1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)) := by
      have h : lowerScale (lowerNormalize p) <
          certThresholdVal (lowerHistoryScaleThreshold (5/7)
            (lowerHistoryWH (([3],[3]) : LowerPair))) (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) := not_le.mp hsh
      have hV : certThresholdVal (lowerHistoryWH (([3],[3]) : LowerPair))
          (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) = ((1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)) / ((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta)) := by
        rw [LowerDev.wh_value]
        show (lowerWidth [3] / lowerWidth [3]) * ((1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)) / ((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta)) = ((1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)) / ((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta))
        rw [div_self (ne_of_gt hW), one_mul]
      rw [LowerDev.scale_value, hV, LowerDev.scale_eq'] at h
      push_cast at h
      rw [show ((5:ℝ)/7) * (((1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)) / ((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta))) = (5 * ((1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta))) / (7 * ((1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).1 * prefixEval [3] lowerBeta))) from by
        field_simp <;> ring, div_lt_div_iff₀ hD2sq (by positivity)] at h
      linarith
    refine ⟨hc.1, hc.2.1, hc.2.2.2, hR, ?_⟩
    show (7/5 : ℝ) * lowerWidth ((lowerNormalize p).2 ++ [3]) <
      lowerWidth ((lowerNormalize p).1 ++ [3])
    rw [LowerDev.width_append, LowerDev.width_append,
      show (7/5 : ℝ) * (lowerWidth [3] /
        ((LowerDev.rCD (lowerNormalize p).2).2 ^ 2 * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)))
        = ((7/5 : ℝ) * lowerWidth [3]) /
        ((LowerDev.rCD (lowerNormalize p).2).2 ^ 2 * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerAlpha) * (1 + lowerRatio (lowerNormalize p).2 * prefixEval [3] lowerBeta)) from by ring,
      div_lt_div_iff₀ hB2 hB1]
    nlinarith [mul_lt_mul_of_pos_left hkey hW]
  -- ==== offered labels ====
  have hLS : ¬ lowerLStar p := by
    intro h
    exact hc.2.2.2 (List.IsSuffix.trans (by decide : ([3,1] : List ℕ+) <:+ [3,1,3,1]) h)
  have hEL : lowerEqualList p =
      (if lowerRStar p then
        [([1],[]),([2],[1]),(if lowerA p 20 then (([3],[1]) : LowerLabel) else ([3],[1,1])),
          ([2],[2])]
      else
        [([1],[]),([2],[1]),(if lowerA p 20 then (([3],[1]) : LowerLabel) else ([3],[1,1])),
          ([2],[2]),([3],[2]),([2],[3])]) := by
    unfold lowerEqualList
    rw [if_neg hc.2.1, if_neg hc.2.2.1, if_neg hLS, if_neg hc.2.2.2]
  have hoffA : lowerOffered p ([1],[]) :=
    Or.inl (by rw [if_neg hc.1, hEL]; split_ifs <;> simp)
  have hoffB : lowerOffered p ([2],[1]) :=
    Or.inl (by rw [if_neg hc.1, hEL]; split_ifs <;> simp)
  have hoffC : lowerOffered p ([2],[2]) :=
    Or.inl (by rw [if_neg hc.1, hEL]; split_ifs <;> simp)
  have hoffd : lowerOffered p (if lowerA p 20 then (([3],[1]) : LowerLabel) else ([3],[1,1])) :=
    Or.inl (by rw [if_neg hc.1, hEL]; split_ifs <;> simp)
  have hoffd1 : lowerA p 20 → lowerOffered p ([3],[1]) := by
    intro h; have := hoffd; rwa [if_pos h] at this
  have hoffd2 : ¬ lowerA p 20 → lowerOffered p ([3],[1,1]) := by
    intro h; have := hoffd; rwa [if_neg h] at this
  have hoffG2 : ¬ lowerRStar p → lowerOffered p ([3],[2]) := by
    intro h; exact Or.inl (by rw [if_neg hc.1, hEL, if_neg h]; simp)
  have hoffE3 : ¬ lowerRStar p → lowerOffered p ([2],[3]) := by
    intro h; exact Or.inl (by rw [if_neg hc.1, hEL, if_neg h]; simp)
  -- ==== the no-run chain ====
  have plainChain : ∀ (dl : LowerLabel) (cuts : List CertBound), lowerOffered p dl →
      TrunkGeometry p ⟨cuts,
        [([1],[]),([2],[1]),dl,([2],[2]),([2],[3]),([3],[2])], []⟩ →
      lowerNumericSuccessor t p := by
    intro dl cuts hoffdl hTG
    by_cases hRS : lowerRStar p
    · refine finish [([2],[1]),dl,([2],[2])] (by simp) ?_ ?_ ?_ ?_
      · refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
          List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩⟩⟩
        · refine hTG.contacts ((([1],[]) : LowerLabel), (([2],[1]) : LowerLabel)) ?_ ?_ <;> simp
        · refine hTG.contacts ((([2],[1]) : LowerLabel), dl) ?_ ?_ <;> simp
        · refine hTG.contacts (dl, (([2],[2]) : LowerLabel)) ?_ ?_ <;> simp
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact ⟨hoffA, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffB, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffdl, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffC, sg _ (hTG.strictGood _ (by simp))⟩
      · exact le_trans hF2.2 (hTG.upper ([1],[]) (by simp))
      · intro a ha
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ha
        subst ha
        exact hb.2.1 hc.1 hc.2.1 hRS
    · refine finish [([2],[1]),dl,([2],[2]),([2],[3]),([3],[2])] (by simp) ?_ ?_ ?_ ?_
      · refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
          List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
          List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩⟩⟩⟩⟩
        · refine hTG.contacts ((([1],[]) : LowerLabel), (([2],[1]) : LowerLabel)) ?_ ?_ <;> simp
        · refine hTG.contacts ((([2],[1]) : LowerLabel), dl) ?_ ?_ <;> simp
        · refine hTG.contacts (dl, (([2],[2]) : LowerLabel)) ?_ ?_ <;> simp
        · refine hTG.contacts ((([2],[2]) : LowerLabel), (([2],[3]) : LowerLabel)) ?_ ?_ <;> simp
        · refine hTG.contacts ((([2],[3]) : LowerLabel), (([3],[2]) : LowerLabel)) ?_ ?_ <;> simp
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hoffA, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffB, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffdl, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffC, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffE3 hRS, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffG2 hRS, sg _ (hTG.strictGood _ (by simp))⟩
      · exact le_trans hF2.2 (hTG.upper ([1],[]) (by simp))
      · intro a ha
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ha
        subst ha
        exact le_trans (hTG.lower ([3],[2]) (by simp)) hF2.1
  -- ==== the chain with the run tail ====
  have runChain : ∀ (dl : LowerLabel) (cuts : List CertBound), lowerOffered p dl →
      lowerRunOffered p →
      TrunkGeometry p ⟨cuts,
        [([1],[]),([2],[1]),dl,([2],[2]),([2],[3]),([3],[2]),([3,3],[3,3]),([3],[3])],
        [((([3,3],[3,3]) : LowerLabel),(([3],[3]) : LowerLabel))]⟩ →
      lowerNumericSuccessor t p := by
    intro dl cuts hoffdl hRO hTG
    obtain ⟨hRgood, hRconn, hRval⟩ := hJ t p ⟨hadm, hgoodp, hcov, hbox⟩ hRO
    have hoffR2 : lowerOffered p ([3,3],[3,3]) := Or.inr ⟨hRO, 2, by norm_num, rfl⟩
    have hgoodR2 : lowerGood (lowerChild p ([3,3],[3,3])) := hRgood 2 (by norm_num)
    by_cases hRS : lowerRStar p
    · refine finish [([2],[1]),dl,([2],[2])] (by simp) ?_ ?_ ?_ ?_
      · refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
          List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩⟩⟩
        · refine hTG.contacts ((([1],[]) : LowerLabel), (([2],[1]) : LowerLabel)) ?_ ?_ <;> simp
        · refine hTG.contacts ((([2],[1]) : LowerLabel), dl) ?_ ?_ <;> simp
        · refine hTG.contacts (dl, (([2],[2]) : LowerLabel)) ?_ ?_ <;> simp
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact ⟨hoffA, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffB, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffdl, sg _ (hTG.strictGood _ (by simp))⟩
        · exact ⟨hoffC, sg _ (hTG.strictGood _ (by simp))⟩
      · exact le_trans hF2.2 (hTG.upper ([1],[]) (by simp))
      · intro a ha
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ha
        subst ha
        exact hb.2.1 hc.1 hc.2.1 hRS
    · by_cases hx : lowerLocalLower p ([3,3],[3,3]) ≤ lowerLocalCoordinate p t
      · refine finish [([2],[1]),dl,([2],[2]),([2],[3]),([3],[2]),([3,3],[3,3])] (by simp)
          ?_ ?_ ?_ ?_
        · refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
            List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
            List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
            List.isChain_singleton _⟩⟩⟩⟩⟩⟩
          · refine hTG.contacts ((([1],[]) : LowerLabel), (([2],[1]) : LowerLabel)) ?_ ?_ <;> simp
          · refine hTG.contacts ((([2],[1]) : LowerLabel), dl) ?_ ?_ <;> simp
          · refine hTG.contacts (dl, (([2],[2]) : LowerLabel)) ?_ ?_ <;> simp
          · refine hTG.contacts ((([2],[2]) : LowerLabel), (([2],[3]) : LowerLabel)) ?_ ?_ <;> simp
          · refine hTG.contacts ((([2],[3]) : LowerLabel), (([3],[2]) : LowerLabel)) ?_ ?_ <;> simp
          · refine hTG.contacts ((([3],[2]) : LowerLabel), (([3,3],[3,3]) : LowerLabel)) ?_ ?_ <;>
              simp
        · intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨hoffA, sg _ (hTG.strictGood _ (by simp))⟩
          · exact ⟨hoffB, sg _ (hTG.strictGood _ (by simp))⟩
          · exact ⟨hoffdl, sg _ (hTG.strictGood _ (by simp))⟩
          · exact ⟨hoffC, sg _ (hTG.strictGood _ (by simp))⟩
          · exact ⟨hoffE3 hRS, sg _ (hTG.strictGood _ (by simp))⟩
          · exact ⟨hoffG2 hRS, sg _ (hTG.strictGood _ (by simp))⟩
          · exact ⟨hoffR2, hgoodR2⟩
        · exact le_trans hF2.2 (hTG.upper ([1],[]) (by simp))
        · intro a ha
          simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ha
          subst ha
          exact hx
      · have hlowR1 : lowerLocalLower p ([3],[3]) ≤ lowerLocalCoordinate p t :=
          le_trans (hTG.lower ([3],[3]) (by simp)) hF2.1
        have hne2 : (lowerCover (lowerChild p ([3,3],[3,3]))).Nonempty :=
          hTG.nonempty _ (by simp)
        have hne1 : (lowerCover (lowerChild p ([3],[3]))).Nonempty := hTG.nonempty _ (by simp)
        have hsub2 : lowerCover (lowerChild p ([3,3],[3,3])) ⊆ lowerRunSet p :=
          fun y hy => Or.inr ⟨2, by norm_num, hy⟩
        have hsub1 : lowerCover (lowerChild p ([3],[3])) ⊆ lowerRunSet p :=
          fun y hy => Or.inr ⟨1, by norm_num, hy⟩
        have hmem : t ∈ lowerRunSet p := by
          push_neg at hx
          simp only [lowerLocalLower, lowerLocalCoordinate] at hx hlowR1
          by_cases hev : (lowerNormalize p).1.length % 2 = 0
          · simp only [hev, if_true] at hx hlowR1
            have hcc2 : lowerEndpoint (lowerChild p ([3,3],[3,3])) false ∈
                lowerCover (lowerChild p ([3,3],[3,3])) := by
              obtain ⟨y, hy⟩ := hne2
              exact Set.mem_Icc.mpr ⟨le_refl _,
                le_trans (Set.mem_Icc.mp hy).1 (Set.mem_Icc.mp hy).2⟩
            have hcc1 : lowerEndpoint (lowerChild p ([3],[3])) false ∈
                lowerCover (lowerChild p ([3],[3])) := by
              obtain ⟨y, hy⟩ := hne1
              exact Set.mem_Icc.mpr ⟨le_refl _,
                le_trans (Set.mem_Icc.mp hy).1 (Set.mem_Icc.mp hy).2⟩
            exact hRconn.Icc_subset (hsub1 hcc1) (hsub2 hcc2)
              (Set.mem_Icc.mpr ⟨hlowR1, le_of_lt hx⟩)
          · simp only [hev, if_false] at hx hlowR1
            have hcc2 : lowerEndpoint (lowerChild p ([3,3],[3,3])) true ∈
                lowerCover (lowerChild p ([3,3],[3,3])) := by
              obtain ⟨y, hy⟩ := hne2
              exact Set.mem_Icc.mpr ⟨le_trans (Set.mem_Icc.mp hy).1 (Set.mem_Icc.mp hy).2,
                le_refl _⟩
            have hcc1 : lowerEndpoint (lowerChild p ([3],[3])) true ∈
                lowerCover (lowerChild p ([3],[3])) := by
              obtain ⟨y, hy⟩ := hne1
              exact Set.mem_Icc.mpr ⟨le_trans (Set.mem_Icc.mp hy).1 (Set.mem_Icc.mp hy).2,
                le_refl _⟩
            exact hRconn.Icc_subset (hsub2 hcc2) (hsub1 hcc1)
              (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        rcases hmem with heq | ⟨kk, hkk, hy⟩
        · exact Or.inl (by rw [heq]; exact hRval)
        · exact Or.inr ⟨(List.replicate kk 3, List.replicate kk 3),
            Or.inr ⟨hRO, kk, hkk, rfl⟩, hRgood kk hkk, hy⟩
  -- ==== the case analysis over the four "large" plans ====
  by_cases hR : lowerR p
  · have hRt : ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.2 :=
      hfit.2.1.2.2.mp hR
    have hplans : trunkSourcePlans (trunkCatalog.states k).context =
        [⟨[lowerHistoryComplement lowerHistoryH7], [([1],[]),([2],[]),([3],[])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryH9,lowerHistoryComplement trunkH18],
          [([1],[]),([2],[]),([3],[2])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryH9,trunkH18],
          [([1],[]),([2],[]),([2],[2]),([3],[2])],
          [((([2],[2]) : LowerLabel),(([3],[2]) : LowerLabel))]⟩,
         ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20],
          [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,lowerHistoryComplement trunkH20],
          [([1],[]),([2],[1]),([3],[1,1]),([2],[2]),([2],[3]),([3],[2])], []⟩] := by
      simp [trunkSourcePlans, hLf, hRt]
    by_cases h20 : lowerA p 20
    · have hpa : trunkPlanAt (trunkCatalog.states k) 3 =
          ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20],
           [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2])], []⟩ := by
        simp [trunkPlanAt, hplans]
      refine plainChain ([3],[1]) [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20] (hoffd1 h20) ?_
      have := hgeom 3 (by rw [hplans]; norm_num) (by
        rw [hpa]
        intro b hb'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
        rcases hb' with rfl | rfl | rfl
        · exact hH7
        · exact hH9c
        · exact hH20 h20)
      rwa [hpa] at this
    · have hpa : trunkPlanAt (trunkCatalog.states k) 4 =
          ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,
            lowerHistoryComplement trunkH20],
           [([1],[]),([2],[1]),([3],[1,1]),([2],[2]),([2],[3]),([3],[2])], []⟩ := by
        simp [trunkPlanAt, hplans]
      refine plainChain ([3],[1,1]) [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,lowerHistoryComplement trunkH20] (hoffd2 h20) ?_
      have := hgeom 4 (by rw [hplans]; norm_num) (by
        rw [hpa]
        intro b hb'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
        rcases hb' with rfl | rfl | rfl
        · exact hH7
        · exact hH9c
        · exact hH20c h20)
      rwa [hpa] at this
  · have hRf : ¬ ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.2 :=
      fun h => hR (hfit.2.1.2.2.mpr h)
    have hplans : trunkSourcePlans (trunkCatalog.states k).context =
        [⟨[lowerHistoryComplement lowerHistoryH7], [([1],[]),([2],[]),([3],[])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryH9,trunkShorten],
          [([1],[]),([2],[]),([3],[2])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryH9,lowerHistoryComplement trunkShorten],
          [([1],[]),([2],[]),([3],[2]),([3,3],[3,3]),([3],[3])],
          [((([3,3],[3,3]) : LowerLabel),(([3],[3]) : LowerLabel))]⟩,
         ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20,trunkShorten],
          [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20,
           lowerHistoryComplement trunkShorten],
          [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2]),([3,3],[3,3]),([3],[3])],
          [((([3,3],[3,3]) : LowerLabel),(([3],[3]) : LowerLabel))]⟩,
         ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,
           lowerHistoryComplement trunkH20,trunkShorten],
          [([1],[]),([2],[1]),([3],[1,1]),([2],[2]),([2],[3]),([3],[2])], []⟩,
         ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,
           lowerHistoryComplement trunkH20,lowerHistoryComplement trunkShorten],
          [([1],[]),([2],[1]),([3],[1,1]),([2],[2]),([2],[3]),([3],[2]),([3,3],[3,3]),([3],[3])],
          [((([3,3],[3,3]) : LowerLabel),(([3],[3]) : LowerLabel))]⟩] := by
      simp [trunkSourcePlans, hLf, hRf]
    by_cases hsh : certBoundHolds trunkShorten (lowerRatio (lowerNormalize p).1)
        (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p))
    · by_cases h20 : lowerA p 20
      · have hpa : trunkPlanAt (trunkCatalog.states k) 3 =
            ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20,trunkShorten],
             [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2])], []⟩ := by
          simp [trunkPlanAt, hplans]
        refine plainChain ([3],[1]) [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20,trunkShorten] (hoffd1 h20) ?_
        have := hgeom 3 (by rw [hplans]; norm_num) (by
          rw [hpa]
          intro b hb'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
          rcases hb' with rfl | rfl | rfl | rfl
          · exact hH7
          · exact hH9c
          · exact hH20 h20
          · exact hsh)
        rwa [hpa] at this
      · have hpa : trunkPlanAt (trunkCatalog.states k) 5 =
            ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,
              lowerHistoryComplement trunkH20,trunkShorten],
             [([1],[]),([2],[1]),([3],[1,1]),([2],[2]),([2],[3]),([3],[2])], []⟩ := by
          simp [trunkPlanAt, hplans]
        refine plainChain ([3],[1,1]) [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,lowerHistoryComplement trunkH20,trunkShorten] (hoffd2 h20) ?_
        have := hgeom 5 (by rw [hplans]; norm_num) (by
          rw [hpa]
          intro b hb'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
          rcases hb' with rfl | rfl | rfl | rfl
          · exact hH7
          · exact hH9c
          · exact hH20c h20
          · exact hsh)
        rwa [hpa] at this
    · have hRO : lowerRunOffered p := hROof hR hsh
      by_cases h20 : lowerA p 20
      · have hpa : trunkPlanAt (trunkCatalog.states k) 4 =
            ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20,
              lowerHistoryComplement trunkShorten],
             [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2]),([3,3],[3,3]),([3],[3])],
             [((([3,3],[3,3]) : LowerLabel),(([3],[3]) : LowerLabel))]⟩ := by
          simp [trunkPlanAt, hplans]
        refine runChain ([3],[1]) [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,trunkH20,lowerHistoryComplement trunkShorten] (hoffd1 h20) hRO ?_
        have := hgeom 4 (by rw [hplans]; norm_num) (by
          rw [hpa]
          intro b hb'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
          rcases hb' with rfl | rfl | rfl | rfl
          · exact hH7
          · exact hH9c
          · exact hH20 h20
          · exact (LowerDev.complement_holds _ _ _ _).mpr hsh)
        rwa [hpa] at this
      · have hpa : trunkPlanAt (trunkCatalog.states k) 6 =
            ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,
              lowerHistoryComplement trunkH20,lowerHistoryComplement trunkShorten],
             [([1],[]),([2],[1]),([3],[1,1]),([2],[2]),([2],[3]),([3],[2]),([3,3],[3,3]),
              ([3],[3])],
             [((([3,3],[3,3]) : LowerLabel),(([3],[3]) : LowerLabel))]⟩ := by
          simp [trunkPlanAt, hplans]
        refine runChain ([3],[1,1]) [lowerHistoryH7,lowerHistoryComplement lowerHistoryH9,lowerHistoryComplement trunkH20,lowerHistoryComplement trunkShorten] (hoffd2 h20) hRO ?_
        have := hgeom 6 (by rw [hplans]; norm_num) (by
          rw [hpa]
          intro b hb'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
          rcases hb' with rfl | rfl | rfl | rfl
          · exact hH7
          · exact hH9c
          · exact hH20c h20
          · exact (LowerDev.complement_holds _ _ _ _).mpr hsh)
        rwa [hpa] at this
