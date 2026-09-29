-- Prove2me | solution 1 for Freiman.middleRepair_cert_endpoint_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T12:39:38.360167+00:00
-- url     : https://prove2.me/submissions/1b8fbd45-2c4c-4031-a8aa-6914591e15fe

import Definitions.Def_Freiman_middleRepairLedger
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

open Freiman

namespace StructuralM8

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

lemma val_alpha : certFieldVal lowerHistoryAlpha = middleAlpha := by
  norm_num [certFieldVal, lowerHistoryAlpha, middleAlpha]; ring
lemma val_beta : certFieldVal lowerHistoryBeta = middleBeta := by
  norm_num [certFieldVal, lowerHistoryBeta, middleBeta]; ring
lemma val_tau : certFieldVal lowerHistoryTau = middleRho := by
  norm_num [certFieldVal, lowerHistoryTau, middleRho]; ring

lemma ab_unit : middleAlpha ∈ Set.Icc (0:ℝ) 1 ∧ middleBeta ∈ Set.Icc (0:ℝ) 1 ∧ middleAlpha < middleBeta := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [middleAlpha, middleBeta]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
lemma rho_unit : middleRho ∈ Set.Icc (0:ℝ) 1 := by
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 3 ≤ (2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [middleRho]
  exact ⟨by linarith, by linarith⟩

/-! ### Continuants and the signed difference identity -/

lemma cd_append (w : List ℕ+) (a : ℕ+) :
    middleCD (w ++ [a]) = ((middleCD w).2, (middleCD w).1 + ((a:ℕ):ℝ) * (middleCD w).2) := by
  simp [middleCD, List.foldl_append]

lemma cd_nil : middleCD [] = (0, 1) := rfl

lemma cd_pos (w : List ℕ+) : 0 ≤ (middleCD w).1 ∧ 0 < (middleCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => rw [cd_nil]; norm_num
  | append_singleton w a ih =>
    rw [cd_append]
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    exact ⟨le_of_lt ih.2, by nlinarith [ih.1, ih.2]⟩

lemma param_nonneg (w : List ℕ+) : 0 ≤ middleParameter w :=
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
      sgnOf w * (x - y) / (((middleCD w).2 + (middleCD w).1 * x) * ((middleCD w).2 + (middleCD w).1 * y)) := by
  induction w using List.reverseRecOn generalizing x y with
  | nil => simp [cd_nil, prefixEval, sgnOf]
  | append_singleton w a ih =>
    obtain ⟨hc, hd⟩ := cd_pos w
    have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hax : 0 < ((a:ℕ):ℝ) + x := by linarith
    have hay : 0 < ((a:ℕ):ℝ) + y := by linarith
    have hx' : 0 ≤ 1 / (((a:ℕ):ℝ) + x) := by positivity
    have hy' : 0 ≤ 1 / (((a:ℕ):ℝ) + y) := by positivity
    have hdx : 0 < (middleCD w).2 + (middleCD w).1 * (1 / (((a:ℕ):ℝ) + x)) := by positivity
    have hdy : 0 < (middleCD w).2 + (middleCD w).1 * (1 / (((a:ℕ):ℝ) + y)) := by positivity
    have hdx' : 0 < (middleCD w).1 + ((a:ℕ):ℝ) * (middleCD w).2 + (middleCD w).2 * x := by positivity
    have hdy' : 0 < (middleCD w).1 + ((a:ℕ):ℝ) * (middleCD w).2 + (middleCD w).2 * y := by positivity
    rw [pe_append, pe_append, pe_single, pe_single, ih _ _ hx' hy', cd_append, sgnOf_append]
    simp only
    field_simp
    try ring

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y =
      sgnOf w * (x - y) /
        ((middleCD w).2 ^ 2 * (1 + middleParameter w * x) * (1 + middleParameter w * y)) := by
  rw [pe_diff_raw w x y hx hy]
  obtain ⟨hc, hd⟩ := cd_pos w
  congr 1
  unfold middleParameter
  field_simp
  try ring

lemma width_eq (w : List ℕ+) :
    middleWidth w = (middleBeta - middleAlpha) /
      ((middleCD w).2 ^ 2 * (1 + middleParameter w * middleAlpha) * (1 + middleParameter w * middleBeta)) := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  unfold middleWidth
  rw [pe_diff w _ _ hb.1 ha.1]
  have hpos : 0 < (middleCD w).2 ^ 2 * (1 + middleParameter w * middleBeta) * (1 + middleParameter w * middleAlpha) := by
    have : 0 ≤ middleParameter w * middleAlpha := mul_nonneg hp ha.1
    have : 0 ≤ middleParameter w * middleBeta := mul_nonneg hp hb.1
    positivity
  rw [abs_div, abs_of_pos hpos, abs_mul]
  have : |sgnOf w| = 1 := by unfold sgnOf; split_ifs <;> simp
  rw [this, one_mul, abs_of_pos (sub_pos.mpr hab)]
  ring

lemma width_pos (w : List ℕ+) : 0 < middleWidth w := by
  obtain ⟨ha, hb, hab⟩ := ab_unit
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  rw [width_eq]
  have : 0 ≤ middleParameter w * middleAlpha := mul_nonneg hp ha.1
  have : 0 ≤ middleParameter w * middleBeta := mul_nonneg hp hb.1
  apply div_pos (sub_pos.mpr hab)
  positivity

lemma width_append (w v : List ℕ+) : middleWidth (w ++ v) =
    middleWidth v / ((middleCD w).2 ^ 2 *
      (1 + middleParameter w * prefixEval v middleAlpha) *
      (1 + middleParameter w * prefixEval v middleBeta)) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have ha := (pe_unit v middleAlpha hA).1
  have hb := (pe_unit v middleBeta hB).1
  have hp := param_nonneg w
  have hd := (cd_pos w).2
  have hpos : 0 < (middleCD w).2 ^ 2 * (1 + middleParameter w * prefixEval v middleBeta) *
      (1 + middleParameter w * prefixEval v middleAlpha) := by
    have : 0 ≤ middleParameter w * prefixEval v middleAlpha := mul_nonneg hp ha
    have : 0 ≤ middleParameter w * prefixEval v middleBeta := mul_nonneg hp hb
    positivity
  unfold middleWidth
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

lemma cf_alpha (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryAlpha) = prefixEval w middleAlpha := by
  rw [cf_correct _ _ (by rw [val_alpha]; exact ab_unit.1.1), val_alpha]
lemma cf_beta (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryBeta) = prefixEval w middleBeta := by
  rw [cf_correct _ _ (by rw [val_beta]; exact ab_unit.2.1.1), val_beta]
lemma cf_tau (w : List ℕ+) : certFieldVal (lowerHistoryCF w lowerHistoryTau) = prefixEval w middleRho := by
  rw [cf_correct _ _ (by rw [val_tau]; exact rho_unit.1), val_tau]

lemma wh_value (w : LowerPair) (r s : ℝ) :
    certThresholdVal (lowerHistoryWH w) r s =
      (middleWidth w.1 / middleWidth w.2) *
        ((1+s*prefixEval w.2 middleAlpha)*(1+s*prefixEval w.2 middleBeta)) /
        ((1+r*prefixEval w.1 middleAlpha)*(1+r*prefixEval w.1 middleBeta)) := by
  have hne : certFieldVal (certFieldSub (lowerHistoryCF w.2 lowerHistoryAlpha)
      (lowerHistoryCF w.2 lowerHistoryBeta)) ≠ 0 := by
    rw [val_sub, cf_alpha, cf_beta]
    have := width_pos w.2
    unfold middleWidth at this
    intro h
    rw [abs_sub_comm, h, abs_zero] at this
    exact lt_irrefl _ this
  unfold lowerHistoryWH
  rw [threshold_value, abs_correct, div_correct _ _ hne, val_sub, val_sub, abs_div]
  simp only [cf_alpha, cf_beta]
  unfold middleWidth
  rw [abs_sub_comm (prefixEval w.1 middleBeta), abs_sub_comm (prefixEval w.2 middleBeta)]

/-- The fundamental width ratio identity: the certificate threshold `WH w` evaluated at the
parameters of `u` and `v`, divided by `q = D_u²/D_v²`, is the width ratio of the extended words. -/
lemma ratio_pair (u v : List ℕ+) (w : LowerPair) :
    middleWidth (u ++ w.1) / middleWidth (v ++ w.2) =
      certThresholdVal (lowerHistoryWH w) (middleParameter u) (middleParameter v) /
        ((middleCD u).2 ^ 2 / (middleCD v).2 ^ 2) := by
  obtain ⟨hA, hB, hab⟩ := ab_unit
  have hup := param_nonneg u
  have hvp := param_nonneg v
  have hud := (cd_pos u).2
  have hvd := (cd_pos v).2
  have ha1 := (pe_unit w.1 middleAlpha hA).1
  have hb1 := (pe_unit w.1 middleBeta hB).1
  have ha2 := (pe_unit w.2 middleAlpha hA).1
  have hb2 := (pe_unit w.2 middleBeta hB).1
  have hw1 := width_pos w.1
  have hw2 := width_pos w.2
  have h1 : 0 < 1 + middleParameter u * prefixEval w.1 middleAlpha := by positivity
  have h2 : 0 < 1 + middleParameter u * prefixEval w.1 middleBeta := by positivity
  have h3 : 0 < 1 + middleParameter v * prefixEval w.2 middleAlpha := by positivity
  have h4 : 0 < 1 + middleParameter v * prefixEval w.2 middleBeta := by positivity
  rw [width_append, width_append, wh_value w]
  field_simp
  try ring

/-! ### Certificate case bookkeeping -/

def normBound (w : LowerPair) (incoming wide : Bool) : CertBound :=
  if wide then ⟨true, !incoming, lowerHistoryWH w⟩ else ⟨false, incoming, lowerHistoryWH w⟩

def cutBound (w : LowerPair) (wide : Bool) (su : List ℕ+) : CertBound :=
  if wide then ⟨false,false,lowerHistoryScaleThreshold (7/5) (lowerHistoryWH (w.1++su,w.2++su))⟩
    else ⟨true,false,lowerHistoryScaleThreshold (5/7) (lowerHistoryWH (w.1++su,w.2++su))⟩

def eqCase (w : LowerPair) (upper parity incoming wide short : Bool) : LowerHistoryEndCase :=
  let e3 := xor (!upper) (middleCertOdd w parity wide)
  let su : List ℕ+ := if e3 then [3] else [1,3]
  let sv : List ℕ+ := if e3 then [2] else [1,2]
  let a := if short then lowerHistoryCF (lowerHistoryPick w wide++su) lowerHistoryTau
    else lowerHistoryCF (lowerHistoryPick w wide) (if e3 then lowerHistoryAlpha else lowerHistoryBeta)
  let b := if short then lowerHistoryCF (lowerHistoryPick w (!wide)++sv) lowerHistoryBeta
    else lowerHistoryCF (lowerHistoryPick w (!wide)++su) lowerHistoryTau
  ((if wide then (b,a) else (a,b)),
    [normBound w incoming wide, if short then cutBound w wide su else lowerHistoryComplement (cutBound w wide su)])

lemma equalCases_eq (w : LowerPair) (upper parity incoming : Bool) :
    middleRepairCertEqualCases w upper parity incoming =
      [eqCase w upper parity incoming false true, eqCase w upper parity incoming false false,
       eqCase w upper parity incoming true true, eqCase w upper parity incoming true false] := rfl

lemma eqCase_mem (w : LowerPair) (upper parity incoming wide short : Bool) :
    eqCase w upper parity incoming wide short ∈ middleRepairCertEqualCases w upper parity incoming := by
  rw [equalCases_eq]
  cases wide <;> cases short <;> simp

lemma endpointCases_equal (w : LowerPair) (upper parity incoming : Bool)
    (h : middleCertOdd w parity false = middleCertOdd w parity true) :
    middleRepairCertEndpointCases w upper parity incoming = middleRepairCertEqualCases w upper parity incoming := by
  unfold middleRepairCertEndpointCases; rw [if_pos h]

lemma endpointCases_mixed_mem (w : LowerPair) (upper parity incoming wide wide' short : Bool)
    (h : ¬ (middleCertOdd w parity false = middleCertOdd w parity true)) :
    ((eqCase (lowerHistorySet w (if (!upper) = middleCertOdd w parity wide then wide else !wide)
        (lowerHistoryPick w (if (!upper) = middleCertOdd w parity wide then wide else !wide)++[1]))
        upper parity wide wide' short).1,
      normBound w incoming wide ::
      (eqCase (lowerHistorySet w (if (!upper) = middleCertOdd w parity wide then wide else !wide)
        (lowerHistoryPick w (if (!upper) = middleCertOdd w parity wide then wide else !wide)++[1]))
        upper parity wide wide' short).2) ∈ middleRepairCertEndpointCases w upper parity incoming := by
  unfold middleRepairCertEndpointCases
  rw [if_neg h, List.mem_flatMap]
  refine ⟨(wide, normBound w incoming wide), ?_, ?_⟩
  · cases wide <;> simp [middleRepairCertNormals, normBound]
  · dsimp only
    rw [List.mem_map]
    exact ⟨_, eqCase_mem _ upper parity wide wide' short, rfl⟩

/-! ### Wide-side selection for the actual core -/

lemma ratio_c (L R : List ℕ+) (w : LowerPair) :
    middleWidth (L ++ w.1) * ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) =
      certThresholdVal (lowerHistoryWH w) (middleParameter L) (middleParameter R) * middleWidth (R ++ w.2) := by
  have h := ratio_pair L R w
  have hB := width_pos (R ++ w.2)
  have hq : 0 < (middleCD L).2 ^ 2 / (middleCD R).2 ^ 2 := by
    have := (cd_pos L).2; have := (cd_pos R).2; positivity
  rw [div_eq_div_iff hB.ne' hq.ne'] at h
  linarith

lemma select_wide (L R : List ℕ+) (w : LowerPair) (incoming : Bool) :
    ∃ wide : Bool,
      middleNormalized (middleRepairAct incoming ⟨L ++ w.1, R ++ w.2⟩) =
        (if wide then ⟨R ++ w.2, L ++ w.1⟩ else ⟨L ++ w.1, R ++ w.2⟩) ∧
      certBoundHolds (normBound w incoming wide) (middleParameter L) (middleParameter R)
        ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) := by
  have hr := ratio_c L R w
  have hA := width_pos (L ++ w.1)
  have hB := width_pos (R ++ w.2)
  have hq : 0 < (middleCD L).2 ^ 2 / (middleCD R).2 ^ 2 := by
    have := (cd_pos L).2; have := (cd_pos R).2; positivity
  set A := middleWidth (L ++ w.1)
  set B := middleWidth (R ++ w.2)
  set q := (middleCD L).2 ^ 2 / (middleCD R).2 ^ 2
  set W := certThresholdVal (lowerHistoryWH w) (middleParameter L) (middleParameter R)
  cases incoming
  · -- not swapped
    simp only [middleRepairAct, Bool.false_eq_true, ↓reduceIte]
    by_cases h : B ≤ A
    · refine ⟨false, ?_, ?_⟩
      · unfold middleNormalized; simp only [middleRepairSwap]; rw [if_pos h]; rfl
      · simp only [normBound, certBoundHolds, Bool.false_eq_true, ↓reduceIte]
        nlinarith
    · refine ⟨true, ?_, ?_⟩
      · unfold middleNormalized; simp only [middleRepairSwap]; rw [if_neg h]; rfl
      · simp only [normBound, certBoundHolds, ↓reduceIte, Bool.not_false]
        have h' := not_le.mp h
        nlinarith
  · -- swapped
    simp only [middleRepairAct, middleRepairSwap, ↓reduceIte]
    by_cases h : A ≤ B
    · refine ⟨true, ?_, ?_⟩
      · unfold middleNormalized; simp only; rw [if_pos h]; rfl
      · simp only [normBound, certBoundHolds, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
        nlinarith
    · refine ⟨false, ?_, ?_⟩
      · unfold middleNormalized; simp only; rw [if_neg h]; rfl
      · simp only [normBound, certBoundHolds, Bool.false_eq_true, ↓reduceIte]
        have h' := not_le.mp h
        nlinarith

lemma cut_iff (L R : List ℕ+) (w : LowerPair) (wide : Bool) (su : List ℕ+) :
    certBoundHolds (cutBound w wide su) (middleParameter L) (middleParameter R)
        ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) ↔
      (if wide then middleWidth (R ++ w.2 ++ su) ≤ (7/5:ℝ) * middleWidth (L ++ w.1 ++ su)
        else middleWidth (L ++ w.1 ++ su) ≤ (7/5:ℝ) * middleWidth (R ++ w.2 ++ su)) := by
  have hr := ratio_c L R (w.1 ++ su, w.2 ++ su)
  simp only [← List.append_assoc] at hr
  have hA := width_pos (L ++ w.1 ++ su)
  have hB := width_pos (R ++ w.2 ++ su)
  have hq : 0 < (middleCD L).2 ^ 2 / (middleCD R).2 ^ 2 := by
    have := (cd_pos L).2; have := (cd_pos R).2; positivity
  cases wide <;>
    simp only [cutBound, certBoundHolds, Bool.false_eq_true, ↓reduceIte, scale_value] <;>
    norm_num only [Rat.cast_div, Rat.cast_ofNat] <;>
    constructor <;> intro h <;> nlinarith

/-! ### Parity bookkeeping -/

lemma odd_pick (L R : List ℕ+) (w : LowerPair) (wide : Bool) :
    middleCertOdd w (decide (L.length % 2 ≠ R.length % 2)) wide =
      xor (decide (L.length % 2 = 1))
        (decide ((if wide then R ++ w.2 else L ++ w.1).length % 2 = 1)) := by
  cases wide
  · simp only [middleCertOdd, lowerHistoryPick, Bool.and_false, Bool.false_xor, Bool.false_eq_true,
      ↓reduceIte, List.length_append]
    rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one w.1.length with h' | h' <;>
    simp [h, h', Nat.add_mod]
  · simp only [middleCertOdd, lowerHistoryPick, Bool.and_true, ↓reduceIte, List.length_append]
    rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one R.length with h'' | h'' <;>
    rcases Nat.mod_two_eq_zero_or_one w.2.length with h' | h' <;>
    simp [h, h', h'', Nat.add_mod]

/-! ### Scalar endpoints -/

noncomputable def scalarEnd (L : List ℕ+) (e : ℝ × ℝ) (upper : Bool) : ℝ :=
  if L.length % 2 = 0 then (if upper then e.2 else e.1) else -(if upper then e.1 else e.2)

lemma endpoint_eq (c : MiddleCore) (w : LowerPair) (upper incoming : Bool) :
    middleRepairCertEndpoint c w upper incoming =
      scalarEnd (middleNormalized c).left
        (middleBounds (middleRepairAct incoming
          ⟨(middleNormalized c).left ++ w.1, (middleNormalized c).right ++ w.2⟩)) upper := rfl

noncomputable def EE (N : MiddleCore) (e3 : Bool) : ℝ := if e3 then middleE3 N else middleE13 N

lemma EE_eq (N : MiddleCore) (e3 : Bool) :
    EE N e3 =
      (if middleWidth (N.left ++ (if e3 then [3] else [1,3])) ≤
          (7/5:ℝ) * middleWidth (N.right ++ (if e3 then [3] else [1,3]))
      then 4 + prefixEval (N.left ++ (if e3 then [3] else [1,3])) middleRho +
        prefixEval (N.right ++ (if e3 then [2] else [1,2])) middleBeta
      else 4 + prefixEval N.left (if e3 then middleAlpha else middleBeta) +
        prefixEval (N.right ++ (if e3 then [3] else [1,3])) middleRho) := by
  cases e3 <;> rfl

lemma scalar_equal_select (L : List ℕ+) (N : MiddleCore) (upper : Bool) :
    scalarEnd L (if N.left.length % 2 = 0 then (middleE3 N, middleE13 N) else (middleE13 N, middleE3 N)) upper
      = sgnOf L * EE N (xor (!upper) (xor (decide (L.length % 2 = 1)) (decide (N.left.length % 2 = 1)))) := by
  cases upper <;>
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one N.left.length with h' | h' <;>
  simp [scalarEnd, sgnOf, EE, h, h']

lemma scalar_mixed_select (L : List ℕ+) (N : MiddleCore) (upper : Bool) (b01 b10 : ℝ × ℝ) :
    scalarEnd L (if N.left.length % 2 = 0 then (b01.1, b10.2) else (b10.1, b01.2)) upper =
      scalarEnd L (if (!upper) = xor (decide (L.length % 2 = 1)) (decide (N.left.length % 2 = 1))
        then b10 else b01) upper := by
  cases upper <;>
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one N.left.length with h' | h' <;>
  simp [scalarEnd, h, h']

lemma holds_cons (b : CertBound) (l : List CertBound) (p s q : ℝ) :
    middleCertHolds (b :: l) p s q ↔ certBoundHolds b p s q ∧ middleCertHolds l p s q := by
  simp [middleCertHolds]

lemma holds_nil (p s q : ℝ) : middleCertHolds [] p s q := by simp [middleCertHolds]

lemma tails_value (L R : List ℕ+) (w : LowerPair) (upper par incoming wide short : Bool) :
    prefixEval L (certFieldVal (eqCase w upper par incoming wide short).1.1) +
      prefixEval R (certFieldVal (eqCase w upper par incoming wide short).1.2) =
    (if short then
        prefixEval ((if wide then R ++ w.2 else L ++ w.1) ++
          (if xor (!upper) (middleCertOdd w par wide) then [3] else [1,3])) middleRho +
        prefixEval ((if wide then L ++ w.1 else R ++ w.2) ++
          (if xor (!upper) (middleCertOdd w par wide) then [2] else [1,2])) middleBeta
      else
        prefixEval (if wide then R ++ w.2 else L ++ w.1)
          (if xor (!upper) (middleCertOdd w par wide) then middleAlpha else middleBeta) +
        prefixEval ((if wide then L ++ w.1 else R ++ w.2) ++
          (if xor (!upper) (middleCertOdd w par wide) then [3] else [1,3])) middleRho) := by
  simp only [eqCase]
  generalize xor (!upper) (middleCertOdd w par wide) = e3
  cases wide <;> cases short <;> cases e3 <;>
    simp [lowerHistoryPick, cf_tau, cf_alpha, cf_beta, pe_append, List.append_assoc] <;> ring

lemma tails_bounds (w : LowerPair) (upper par incoming wide short : Bool) :
    certFieldVal (eqCase w upper par incoming wide short).1.1 ∈ Set.Icc (0:ℝ) 1 ∧
    certFieldVal (eqCase w upper par incoming wide short).1.2 ∈ Set.Icc (0:ℝ) 1 := by
  have hA := ab_unit.1
  have hB := ab_unit.2.1
  have hT := rho_unit
  simp only [eqCase]
  generalize xor (!upper) (middleCertOdd w par wide) = e3
  cases wide <;> cases short <;> cases e3 <;>
    simp only [lowerHistoryPick, cf_tau, cf_alpha, cf_beta, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true] <;>
    exact ⟨pe_unit _ _ (by assumption), pe_unit _ _ (by assumption)⟩

lemma normalized_idem (c : MiddleCore) :
    middleNormalized (middleNormalized c) = middleNormalized c := by
  unfold middleNormalized
  split_ifs <;> first | rfl | (simp_all only [not_le]; order)

/-- Equal-parity realization: the actual `E₃/E₁₃` endpoint of a normalized child `N` is one of the
enumerated alternatives, whose conditions hold. -/
lemma equal_realize (L R : List ℕ+) (w : LowerPair) (upper incoming wide : Bool) (N : MiddleCore)
    (hN : N = (if wide then ⟨R ++ w.2, L ++ w.1⟩ else ⟨L ++ w.1, R ++ w.2⟩))
    (hnorm : certBoundHolds (normBound w incoming wide) (middleParameter L) (middleParameter R)
      ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2)) :
    ∃ short : Bool,
      middleCertHolds (eqCase w upper (decide (L.length % 2 ≠ R.length % 2)) incoming wide short).2
        (middleParameter L) (middleParameter R) ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) ∧
      scalarEnd L (if N.left.length % 2 = 0 then (middleE3 N, middleE13 N) else (middleE13 N, middleE3 N)) upper
        = sgnOf L * (4 + prefixEval L (certFieldVal
            (eqCase w upper (decide (L.length % 2 ≠ R.length % 2)) incoming wide short).1.1)
          + prefixEval R (certFieldVal
            (eqCase w upper (decide (L.length % 2 ≠ R.length % 2)) incoming wide short).1.2)) := by
  set par := decide (L.length % 2 ≠ R.length % 2) with hpar
  have hodd : middleCertOdd w par wide = xor (decide (L.length % 2 = 1)) (decide (N.left.length % 2 = 1)) := by
    rw [hpar, odd_pick, hN]; cases wide <;> rfl
  rw [scalar_equal_select, ← hodd, EE_eq]
  have hL : N.left = (if wide then R ++ w.2 else L ++ w.1) := by rw [hN]; cases wide <;> rfl
  have hR : N.right = (if wide then L ++ w.1 else R ++ w.2) := by rw [hN]; cases wide <;> rfl
  set e3 := xor (!upper) (middleCertOdd w par wide) with he3
  have hcut : ∀ short : Bool, (eqCase w upper par incoming wide short).2 =
      [normBound w incoming wide, if short then cutBound w wide (if e3 then [3] else [1,3])
        else lowerHistoryComplement (cutBound w wide (if e3 then [3] else [1,3]))] := by
    intro short; rfl
  have hcond : (middleWidth (N.left ++ (if e3 then [3] else [1,3])) ≤
      (7/5:ℝ) * middleWidth (N.right ++ (if e3 then [3] else [1,3]))) ↔
      certBoundHolds (cutBound w wide (if e3 then [3] else [1,3])) (middleParameter L) (middleParameter R)
        ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) := by
    rw [cut_iff, hL, hR]; cases wide <;> simp
  by_cases hs : middleWidth (N.left ++ (if e3 then [3] else [1,3])) ≤
      (7/5:ℝ) * middleWidth (N.right ++ (if e3 then [3] else [1,3]))
  · refine ⟨true, ?_, ?_⟩
    · rw [hcut, holds_cons, holds_cons]
      exact ⟨hnorm, by simpa using hcond.mp hs, holds_nil _ _ _⟩
    · have hv := tails_value L R w upper par incoming wide true
      rw [← he3] at hv
      simp only [↓reduceIte] at hv
      rw [if_pos hs, hL, hR, add_assoc (4:ℝ) (prefixEval L _), hv]
      ring
  · refine ⟨false, ?_, ?_⟩
    · rw [hcut, holds_cons, holds_cons]
      refine ⟨hnorm, ?_, holds_nil _ _ _⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [complement_holds]
      exact fun h => hs (hcond.mpr h)
    · have hv := tails_value L R w upper par incoming wide false
      rw [← he3] at hv
      simp only [Bool.false_eq_true, ↓reduceIte] at hv
      rw [if_neg hs, hL, hR, add_assoc (4:ℝ) (prefixEval L _), hv]
      ring

lemma mixed_core (L R : List ℕ+) (w : LowerPair) (wide side : Bool) (N : MiddleCore)
    (hN : N = (if wide then ⟨R ++ w.2, L ++ w.1⟩ else ⟨L ++ w.1, R ++ w.2⟩)) :
    middleRepairAct wide ⟨L ++ (lowerHistorySet w side (lowerHistoryPick w side ++ [1])).1,
        R ++ (lowerHistorySet w side (lowerHistoryPick w side ++ [1])).2⟩ =
      (if side = wide then ⟨N.left ++ [1], N.right⟩ else ⟨N.left, N.right ++ [1]⟩) := by
  subst hN
  cases wide <;> cases side <;>
    simp [middleRepairAct, middleRepairSwap, lowerHistorySet, lowerHistoryPick, List.append_assoc]

lemma parity_transfer (L R : List ℕ+) (w : LowerPair) :
    (middleCertOdd w (decide (L.length % 2 ≠ R.length % 2)) false =
      middleCertOdd w (decide (L.length % 2 ≠ R.length % 2)) true) ↔
    ((L ++ w.1).length % 2 = (R ++ w.2).length % 2) := by
  rw [odd_pick, odd_pick]
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_append]
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one (L.length + w.1.length) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (R.length + w.2.length) with h2 | h2 <;>
  simp [h, h1, h2]

/-- **Endpoint realization.** Every actual endpoint of a child of the normalized core is one of the
enumerated certificate alternatives; the alternative's conditions hold at `(p,s,q)`, and the endpoint
equals `sgn · (4 + T_L(x) + T_R(y))` for the alternative's tails `(x,y)`. -/
theorem realize (c : MiddleCore) (w : LowerPair) (upper incoming : Bool) :
    ∃ x y : CertField, ∃ cs : List CertBound,
      ((x,y),cs) ∈ middleRepairCertEndpointCases w upper
          (decide ((middleNormalized c).left.length % 2 ≠ (middleNormalized c).right.length % 2)) incoming ∧
      middleCertHolds cs (middleParameter (middleNormalized c).left)
        (middleParameter (middleNormalized c).right) (middleQ c) ∧
      middleRepairCertEndpoint c w upper incoming =
        sgnOf (middleNormalized c).left * (4 + prefixEval (middleNormalized c).left (certFieldVal x) +
          prefixEval (middleNormalized c).right (certFieldVal y)) ∧
      certFieldVal x ∈ Set.Icc (0:ℝ) 1 ∧ certFieldVal y ∈ Set.Icc (0:ℝ) 1 := by
  have hq : middleQ c = (middleCD (middleNormalized c).left).2 ^ 2 / (middleCD (middleNormalized c).right).2 ^ 2 := rfl
  rw [hq, endpoint_eq]
  set L := (middleNormalized c).left with hL
  set R := (middleNormalized c).right with hR
  set par := decide (L.length % 2 ≠ R.length % 2) with hpar
  obtain ⟨wide, hN, hnorm⟩ := select_wide L R w incoming
  set N := middleNormalized (middleRepairAct incoming ⟨L ++ w.1, R ++ w.2⟩) with hNdef
  have hbounds : middleBounds (middleRepairAct incoming ⟨L ++ w.1, R ++ w.2⟩) =
      (if N.left.length % 2 = N.right.length % 2 then middleEqualBounds N else
        (if N.left.length % 2 = 0 then
          ((middleEqualBounds ⟨N.left, N.right ++ [1]⟩).1, (middleEqualBounds ⟨N.left ++ [1], N.right⟩).2)
         else ((middleEqualBounds ⟨N.left ++ [1], N.right⟩).1, (middleEqualBounds ⟨N.left, N.right ++ [1]⟩).2))) := rfl
  rw [hbounds]
  have hNl : N.left = (if wide then R ++ w.2 else L ++ w.1) := by rw [hN]; cases wide <;> rfl
  have hNr : N.right = (if wide then L ++ w.1 else R ++ w.2) := by rw [hN]; cases wide <;> rfl
  have hpt := parity_transfer L R w
  by_cases heq : middleCertOdd w par false = middleCertOdd w par true
  · -- equal parities
    have hsame : N.left.length % 2 = N.right.length % 2 := by
      have := hpt.mp heq
      rw [hNl, hNr]; cases wide <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    rw [if_pos hsame]
    have hNN : middleNormalized N = N := by rw [hNdef]; exact normalized_idem _
    have hEB : middleEqualBounds N =
        (if N.left.length % 2 = 0 then (middleE3 N, middleE13 N) else (middleE13 N, middleE3 N)) := by
      simp only [middleEqualBounds, hNN]
    rw [hEB]
    obtain ⟨short, h1, h2⟩ := equal_realize L R w upper incoming wide N hN hnorm
    refine ⟨_, _, _, ?_, h1, h2, tails_bounds w upper par incoming wide short⟩
    rw [endpointCases_equal w upper par incoming heq]
    exact eqCase_mem _ _ _ _ _ _
  · -- mixed parities
    have hdiff : ¬ N.left.length % 2 = N.right.length % 2 := by
      have := mt hpt.mpr heq
      rw [hNl, hNr]; cases wide <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    rw [if_neg hdiff, scalar_mixed_select]
    have hodd : middleCertOdd w par wide = xor (decide (L.length % 2 = 1)) (decide (N.left.length % 2 = 1)) := by
      rw [hpar, odd_pick, hN]; cases wide <;> rfl
    rw [← hodd]
    set side := (if (!upper) = middleCertOdd w par wide then wide else !wide) with hside
    set nw := lowerHistorySet w side (lowerHistoryPick w side ++ [1]) with hnw
    have hM : (if (!upper) = middleCertOdd w par wide then middleEqualBounds ⟨N.left ++ [1], N.right⟩
        else middleEqualBounds ⟨N.left, N.right ++ [1]⟩) =
        middleEqualBounds (middleRepairAct wide ⟨L ++ nw.1, R ++ nw.2⟩) := by
      rw [hnw, mixed_core L R w wide side N hN]
      by_cases h : (!upper) = middleCertOdd w par wide
      · rw [if_pos h]
        have : side = wide := by rw [hside, if_pos h]
        rw [if_pos this]
      · rw [if_neg h]
        have : ¬ side = wide := by rw [hside, if_neg h]; cases wide <;> simp
        rw [if_neg this]
    rw [hM]
    obtain ⟨wide', hM', hnorm'⟩ := select_wide L R nw wide
    set M := middleNormalized (middleRepairAct wide ⟨L ++ nw.1, R ++ nw.2⟩) with hMdef
    have hEB : middleEqualBounds (middleRepairAct wide ⟨L ++ nw.1, R ++ nw.2⟩) =
        (if M.left.length % 2 = 0 then (middleE3 M, middleE13 M) else (middleE13 M, middleE3 M)) := rfl
    rw [hEB]
    obtain ⟨short, h1, h2⟩ := equal_realize L R nw upper wide wide' M hM' hnorm'
    refine ⟨_, _, _, endpointCases_mixed_mem w upper par incoming wide wide' short heq, ?_, h2,
      tails_bounds nw upper par wide wide' short⟩
    rw [holds_cons]
    exact ⟨hnorm, h1⟩

/-! ### Comparison semantics -/

lemma sgnOf_mul_sgnOf (L R : List ℕ+) :
    sgnOf L * sgnOf R = (if decide (L.length % 2 ≠ R.length % 2) then (-1:ℝ) else 1) := by
  unfold sgnOf
  rcases Nat.mod_two_eq_zero_or_one L.length with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one R.length with h' | h' <;> simp [h, h']

lemma scalar_diff (L R : List ℕ+) (x1 y1 x2 y2 : ℝ)
    (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1) (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) :
    sgnOf L * (prefixEval L x1 + prefixEval R x2) - sgnOf L * (prefixEval L y1 + prefixEval R y2) =
      (x1 - y1) / ((middleCD L).2 ^ 2 * (1 + middleParameter L * x1) * (1 + middleParameter L * y1)) +
      (if decide (L.length % 2 ≠ R.length % 2) then (-1:ℝ) else 1) *
        ((x2 - y2) / ((middleCD R).2 ^ 2 * (1 + middleParameter R * x2) * (1 + middleParameter R * y2))) := by
  have h1 := pe_diff L x1 y1 hx1 hy1
  have h2 := pe_diff R x2 y2 hx2 hy2
  have hs := sgnOf_sq L
  rw [← sgnOf_mul_sgnOf]
  have e : sgnOf L * (prefixEval L x1 + prefixEval R x2) - sgnOf L * (prefixEval L y1 + prefixEval R y2) =
      sgnOf L * (prefixEval L x1 - prefixEval L y1) + sgnOf L * (prefixEval R x2 - prefixEval R y2) := by ring
  rw [e, h1, h2]
  linear_combination ((x1 - y1) /
    ((middleCD L).2 ^ 2 * (1 + middleParameter L * x1) * (1 + middleParameter L * y1))) * hs

lemma eps_spec (par : Bool) (z : CertField) :
    (0 ≤ (if par then (-1:ℤ) else 1) * lowerHistorySign z →
      0 ≤ (if par then (-1:ℝ) else 1) * certFieldVal z) ∧
    ((if par then (-1:ℤ) else 1) * lowerHistorySign z ≤ 0 →
      (if par then (-1:ℝ) else 1) * certFieldVal z ≤ 0) ∧
    (0 < (if par then (-1:ℤ) else 1) * lowerHistorySign z →
      0 < (if par then (-1:ℝ) else 1) * certFieldVal z) ∧
    ((if par then (-1:ℤ) else 1) * lowerHistorySign z < 0 →
      (if par then (-1:ℝ) else 1) * certFieldVal z < 0) := by
  cases par
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact ⟨sign_nonneg_of z, sign_nonpos_of z, (sign_spec z).1, (sign_spec z).2.1⟩
  · simp only [↓reduceIte, neg_mul, one_mul]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := sign_nonpos_of z (by linarith); linarith
    · have := sign_nonneg_of z (by linarith); linarith
    · have := (sign_spec z).2.1 (by linarith); linarith
    · have := (sign_spec z).1 (by linarith); linarith

lemma val_ne_zero_of_sign (z : CertField) (h : lowerHistorySign z ≠ 0) : certFieldVal z ≠ 0 := by
  intro h0
  rcases lt_trichotomy (lowerHistorySign z) 0 with h1 | h1 | h1
  · exact absurd h0 (ne_of_lt ((sign_spec z).2.1 h1))
  · exact h h1
  · exact absurd h0 (ne_of_gt ((sign_spec z).1 h1))

/-- The real comparison of two endpoint sums in the scalar coordinate. -/
def RI (L R : List ℕ+) (x y : CertField × CertField) : Prop :=
  sgnOf L * (prefixEval L (certFieldVal y.1) + prefixEval R (certFieldVal y.2)) ≤
  sgnOf L * (prefixEval L (certFieldVal x.1) + prefixEval R (certFieldVal x.2))

/-- **Comparison semantics.** The symbolic comparison `middleCertGreater` is faithful to the
real endpoint comparison. -/
lemma greater_spec (L R : List ℕ+) (x y : CertField × CertField)
    (hx1 : 0 ≤ certFieldVal x.1) (hy1 : 0 ≤ certFieldVal y.1)
    (hx2 : 0 ≤ certFieldVal x.2) (hy2 : 0 ≤ certFieldVal y.2) :
    match middleCertGreater (decide (L.length % 2 ≠ R.length % 2)) x y with
    | .automatic => RI L R x y
    | .impossible => ¬ RI L R x y
    | .bound b => (certBoundHolds b (middleParameter L) (middleParameter R)
        ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) ↔ RI L R x y) := by
  set par := decide (L.length % 2 ≠ R.length % 2) with hpar
  have hdiff := scalar_diff L R _ _ _ _ hx1 hy1 hx2 hy2
  rw [← hpar] at hdiff
  have hDL := (cd_pos L).2
  have hDR := (cd_pos R).2
  have hp := param_nonneg L
  have hs := param_nonneg R
  have hPx : 0 < (1 + middleParameter L * certFieldVal x.1) * (1 + middleParameter L * certFieldVal y.1) := by
    positivity
  have hPy : 0 < (1 + middleParameter R * certFieldVal x.2) * (1 + middleParameter R * certFieldVal y.2) := by
    positivity
  have hPA : 0 < (middleCD L).2 ^ 2 * (1 + middleParameter L * certFieldVal x.1) *
      (1 + middleParameter L * certFieldVal y.1) := by positivity
  have hPB : 0 < (middleCD R).2 ^ 2 * (1 + middleParameter R * certFieldVal x.2) *
      (1 + middleParameter R * certFieldVal y.2) := by positivity
  have hDL2 : 0 < (middleCD L).2 ^ 2 := by positivity
  have hDR2 : 0 < (middleCD R).2 ^ 2 := by positivity
  set ε : ℝ := (if par then -1 else 1) with hε
  set Px := (1 + middleParameter L * certFieldVal x.1) * (1 + middleParameter L * certFieldVal y.1) with hPxd
  set Py := (1 + middleParameter R * certFieldVal x.2) * (1 + middleParameter R * certFieldVal y.2) with hPyd
  set PA := (middleCD L).2 ^ 2 * (1 + middleParameter L * certFieldVal x.1) *
      (1 + middleParameter L * certFieldVal y.1) with hPAd
  set PB := (middleCD R).2 ^ 2 * (1 + middleParameter R * certFieldVal x.2) *
      (1 + middleParameter R * certFieldVal y.2) with hPBd
  have hPAe : PA = (middleCD L).2 ^ 2 * Px := by rw [hPAd, hPxd]; ring
  have hPBe : PB = (middleCD R).2 ^ 2 * Py := by rw [hPBd, hPyd]; ring
  set Dx := certFieldVal x.1 - certFieldVal y.1 with hDx
  set Dy := certFieldVal x.2 - certFieldVal y.2 with hDy
  have hRI : RI L R x y ↔ 0 ≤ Dx * PB + ε * Dy * PA := by
    unfold RI
    rw [← sub_nonneg, hdiff]
    have : Dx / PA + ε * (Dy / PB) = (Dx * PB + ε * Dy * PA) / (PA * PB) := by
      field_simp
    rw [this, le_div_iff₀ (mul_pos hPA hPB), zero_mul]
  have hval_dx : certFieldVal (certFieldSub x.1 y.1) = Dx := val_sub _ _
  have hval_dy : certFieldVal (certFieldSub x.2 y.2) = Dy := val_sub _ _
  obtain ⟨e1, e2, e3, e4⟩ := eps_spec par (certFieldSub x.2 y.2)
  rw [hval_dy, ← hε] at e1 e2 e3 e4
  obtain ⟨sg1, sg2, sg3⟩ := sign_spec (certFieldSub x.1 y.1)
  have sg4 := sign_nonneg_of (certFieldSub x.1 y.1)
  have sg5 := sign_nonpos_of (certFieldSub x.1 y.1)
  rw [hval_dx] at sg1 sg2 sg3 sg4 sg5
  have habsε : |ε| = 1 := by rw [hε]; split_ifs <;> simp
  simp only [middleCertGreater, lowerHistoryGreater, Bool.false_eq_true, ↓reduceIte, one_mul]
  generalize hεz : (if par = true then (-1:ℤ) else 1) = εz at e1 e2 e3 e4 ⊢
  by_cases h1 : 0 ≤ lowerHistorySign (certFieldSub x.1 y.1) ∧ 0 ≤ εz * lowerHistorySign (certFieldSub x.2 y.2)
  · -- automatic
    rw [if_pos h1]
    show RI L R x y
    rw [hRI]
    have hx := sg4 h1.1
    have hy := e1 h1.2
    linarith only [mul_nonneg hx hPB.le, mul_nonneg hy hPA.le]
  rw [if_neg h1]
  by_cases h2 : lowerHistorySign (certFieldSub x.1 y.1) ≤ 0 ∧ εz * lowerHistorySign (certFieldSub x.2 y.2) ≤ 0
  · -- impossible
    rw [if_pos h2]
    show ¬ RI L R x y
    rw [hRI]
    have hx := sg5 h2.1
    have hy := e2 h2.2
    rcases not_and_or.mp h1 with h1 | h1
    · have hx' := sg2 (lt_of_not_ge h1)
      linarith only [mul_pos (neg_pos.mpr hx') hPB, mul_nonneg (neg_nonneg.mpr hy) hPA.le]
    · have hy' := e4 (lt_of_not_ge h1)
      linarith only [mul_pos (neg_pos.mpr hy') hPA, mul_nonneg (neg_nonneg.mpr hx) hPB.le]
  -- bound
  rewrite [if_neg h2]
  show certBoundHolds ⟨decide (lowerHistorySign (certFieldSub x.1 y.1) < 0), false,
      lowerHistoryThreshold (lowerHistoryAbs (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2)))
        (x.1, y.1) (x.2, y.2)⟩ (middleParameter L) (middleParameter R)
      ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) ↔ RI L R x y
  have hdy : Dy ≠ 0 := by
    rw [← hval_dy]
    apply val_ne_zero_of_sign
    intro h0
    rw [h0, mul_zero] at h1 h2
    omega
  have hthr : certThresholdVal (lowerHistoryThreshold
      (lowerHistoryAbs (lowerHistoryDiv (certFieldSub x.1 y.1) (certFieldSub x.2 y.2)))
      (x.1, y.1) (x.2, y.2)) (middleParameter L) (middleParameter R) = |Dx / Dy| * Py / Px := by
    rw [threshold_value, abs_correct, div_correct _ _ (by rw [hval_dy]; exact hdy), hval_dx, hval_dy]
  by_cases hsx : lowerHistorySign (certFieldSub x.1 y.1) < 0
  · have hDxn : Dx < 0 := sg2 hsx
    have hεy : 0 < ε * Dy := by
      apply e3
      by_contra hc
      exact h2 ⟨hsx.le, not_lt.mp hc⟩
    simp only [certBoundHolds, hsx, decide_true, ↓reduceIte, Bool.false_eq_true]
    rw [hthr, hRI]
    have habs : |Dx / Dy| = (-Dx) / (ε * Dy) := by
      rw [abs_div, abs_of_neg hDxn]
      congr 1
      rw [← abs_of_pos hεy, abs_mul, habsε, one_mul]
    rw [habs, div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [hPAe, hPBe]
    constructor <;> intro h <;> linarith only [h]
  · have hsx' : 0 < lowerHistorySign (certFieldSub x.1 y.1) := by
      rcases lt_or_eq_of_le (not_lt.mp hsx) with h | h
      · exact h
      · exfalso
        have : εz * lowerHistorySign (certFieldSub x.2 y.2) < 0 := by
          by_contra hc
          exact h1 ⟨le_of_eq h, not_lt.mp hc⟩
        exact h2 ⟨le_of_eq h.symm, this.le⟩
    have hDxp : 0 < Dx := sg1 hsx'
    have hεy : ε * Dy < 0 := by
      apply e4
      by_contra hc
      exact h1 ⟨hsx'.le, not_lt.mp hc⟩
    simp only [certBoundHolds, hsx, decide_false, ↓reduceIte, Bool.false_eq_true]
    rw [hthr, hRI]
    have habs : |Dx / Dy| = Dx / (-(ε * Dy)) := by
      rw [abs_div, abs_of_pos hDxp]
      congr 1
      rw [← abs_of_neg hεy, abs_mul, habsε, one_mul]
    rw [habs, div_mul_eq_mul_div, div_div,
      div_le_div_iff₀ (by positivity) (mul_pos (neg_pos.mpr hεy) hPx)]
    rw [hPAe, hPBe]
    constructor <;> intro h <;> linarith only [h]

/-! ### Final assembly -/

lemma holds_append (l m : List CertBound) (p s q : ℝ) :
    middleCertHolds (l ++ m) p s q ↔ middleCertHolds l p s q ∧ middleCertHolds m p s q := by
  simp [middleCertHolds, List.mem_append, or_imp, forall_and]

lemma domain_parity (c : MiddleCore) (f : Fin 11) (hd : middleRepairCertDomain c f.val) :
    decide ((middleNormalized c).left.length % 2 ≠ (middleNormalized c).right.length % 2) =
      middleCertParity f.val := by
  fin_cases f <;>
    norm_num [middleRepairCertDomain, middleRowCondition, middleCertRow, middleCertParity] at hd ⊢ <;>
    tauto

lemma bounds_normalized (X : MiddleCore) : middleBounds (middleNormalized X) = middleBounds X := by
  simp only [middleBounds, normalized_idem]

lemma child_endpoint (c : MiddleCore) (u : List ℕ+) (upper : Bool) :
    middleRepairCertEndpoint c (u, []) upper false =
      scalarEnd (middleNormalized c).left (middleBounds (middleRepairChild c u [])) upper := by
  rw [endpoint_eq]
  unfold middleRepairChild middleRepairRawChild
  rw [bounds_normalized]
  rfl

lemma normalized_width_order (c : MiddleCore) :
    middleWidth (middleNormalized c).right ≤ middleWidth (middleNormalized c).left := by
  unfold middleNormalized
  split_ifs with h
  · exact h
  · exact le_of_lt (lt_of_not_ge h)

lemma norm0_holds (c : MiddleCore) :
    certBoundHolds ⟨false,false,lowerHistoryWH ([],[])⟩ (middleParameter (middleNormalized c).left)
      (middleParameter (middleNormalized c).right) (middleQ c) := by
  have hr := ratio_c (middleNormalized c).left (middleNormalized c).right ([],[])
  simp only [List.append_nil] at hr
  have hA := width_pos (middleNormalized c).left
  have hB := width_pos (middleNormalized c).right
  have hAB := normalized_width_order c
  have hq : 0 < (middleCD (middleNormalized c).left).2 ^ 2 / (middleCD (middleNormalized c).right).2 ^ 2 := by
    have := (cd_pos (middleNormalized c).left).2; have := (cd_pos (middleNormalized c).right).2
    positivity
  show (middleCD (middleNormalized c).left).2 ^ 2 / (middleCD (middleNormalized c).right).2 ^ 2 ≤
    certThresholdVal (lowerHistoryWH ([],[])) (middleParameter (middleNormalized c).left)
      (middleParameter (middleNormalized c).right)
  have hWB : 0 < certThresholdVal (lowerHistoryWH ([],[])) (middleParameter (middleNormalized c).left)
      (middleParameter (middleNormalized c).right) * middleWidth (middleNormalized c).right := by
    rw [← hr]; positivity
  have hW := pos_of_mul_pos_left hWB hB.le
  nlinarith [mul_le_mul_of_nonneg_left hAB hW.le]

end StructuralM8

open StructuralM8

theorem solution :
    ∀ (C : MiddleCertCatalog) (c : MiddleCore) (f : Fin 11) (g : MiddleCertGoal) (sp : MiddleCertSpec), middleRepairCertDomain c f.val → g.family=f.val → middleCertGoalMatches C g sp → (∀ j ∈ List.range (middleRepairCertGoalBranches C g).length, middleCertHolds (middleRepairCertBranch C g j).1 (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c) → middleCertComparisonHolds (middleRepairCertBranch C g j).2 (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) (middleQ c)) → middleRepairCertSpecHolds c sp := by
  intro C c f g sp hd hfam hmatch hbr _hextra
  obtain ⟨_, _, _, _, hrole, hw1, hu1, hw2, hu2, _, _, _⟩ := hmatch
  have hpar := domain_parity c f hd
  set L := (middleNormalized c).left with hL
  set R := (middleNormalized c).right with hR
  set par := decide (L.length % 2 ≠ R.length % 2) with hpardef
  have hB : middleRepairCertGoalBranches C g =
      middleRepairCertCompare sp.first sp.second sp.firstUpper sp.secondUpper par
        (middleRepairCertIncoming sp.role) := by
    simp only [middleRepairCertGoalBranches]
    rw [hw1, hu1, hw2, hu2, hrole, hfam, hpar]
  obtain ⟨x1, x2, cx, hmx, hhx, hEx, hbx1, hbx2⟩ :=
    realize c sp.first sp.firstUpper (middleRepairCertIncoming sp.role)
  obtain ⟨y1, y2, cy, hmy, hhy, hEy, hby1, hby2⟩ :=
    realize c sp.second sp.secondUpper (middleRepairCertIncoming sp.role)
  have hmem : (cx ++ cy, middleCertGreater par (x1,x2) (y1,y2)) ∈ middleRepairCertGoalBranches C g := by
    rw [hB]
    unfold middleRepairCertCompare
    rw [List.mem_flatMap]
    exact ⟨((x1,x2),cx), hmx, List.mem_map.mpr ⟨((y1,y2),cy), hmy, rfl⟩⟩
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
  have hbranch : middleRepairCertBranch C g j = (cx ++ cy, middleCertGreater par (x1,x2) (y1,y2)) := by
    unfold middleRepairCertBranch
    rw [List.getElem?_eq_getElem hj, hjeq]
    rfl
  have hcomp := hbr j (List.mem_range.mpr hj) (by rw [hbranch]; exact (holds_append _ _ _ _ _).mpr ⟨hhx, hhy⟩)
  rw [hbranch] at hcomp
  have hq' : middleQ c = (middleCD L).2 ^ 2 / (middleCD R).2 ^ 2 := rfl
  have gs := greater_spec L R (x1,x2) (y1,y2) hbx1.1 hby1.1 hbx2.1 hby2.1
  have hRI : RI L R (x1,x2) (y1,y2) := by
    rcases hG : middleCertGreater par (x1,x2) (y1,y2) with _ | _ | b
    · rw [hG] at gs; exact gs
    · rw [hG] at hcomp
      exact absurd hcomp id
    · rw [hG] at hcomp gs
      rw [hq'] at hcomp
      have gs' : certBoundHolds b (middleParameter L) (middleParameter R)
          ((middleCD L).2 ^ 2 / (middleCD R).2 ^ 2) ↔ RI L R (x1,x2) (y1,y2) := gs
      exact gs'.mp hcomp
  rw [hEx, hEy]
  unfold RI at hRI
  simp only at hRI
  linarith
