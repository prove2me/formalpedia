-- Prove2me | solution 1 for BookProof.ScalaronEdge.edge_sup_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:43:50.305503+00:00
-- url     : https://prove2.me/submissions/03387257-eea6-4607-9a8b-e22ee35039a3

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edge_sup_sq_le
import Mathlib
import Definitions.Def_ChapterScalaronEdge
import Theorems.Thm_BookProof_ScalaronEdge_edge_normSq_hasDerivAt
import Theorems.Thm_BookProof_ScalaronEdge_edge_re_mul_le
open BookProof.ScalaronEdge










open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖f x‖ ^ 2 ≤ ∫ t, (δ * ‖f t‖ ^ 2 + δ⁻¹ * ‖deriv f t‖ ^ 2) := by

  set g' : ℝ → ℝ := fun t =>
    ((starRingEnd ℂ) (deriv f t) * f t + (starRingEnd ℂ) (f t) * deriv f t).re with hg'def
  set h : ℝ → ℝ := fun t => δ * ‖f t‖ ^ 2 + δ⁻¹ * ‖deriv f t‖ ^ 2 with hhdef
  have hcont0 : Continuous f := hf.continuous
  have hcont1 : Continuous (deriv f) := (hf.deriv' (n := 1)).continuous
  have hs1 : HasCompactSupport (deriv f) := hs.deriv
  have hgc : Continuous g' := by rw [hg'def]; fun_prop
  have hhc : Continuous h := by rw [hhdef]; fun_prop
  have hhsupp : HasCompactSupport h :=
    HasCompactSupport.add (hs.comp_left (g := fun z : ℂ => δ * ‖z‖ ^ 2) (by simp))
      (hs1.comp_left (g := fun z : ℂ => δ⁻¹ * ‖z‖ ^ 2) (by simp))
  have hhint : Integrable h := hhc.integrable_of_hasCompactSupport hhsupp
  have hhnn : ∀ t, 0 ≤ h t := fun t => by rw [hhdef]; positivity
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  set y : ℝ := min x (-|R| - 1) with hydef
  have hyx : y ≤ x := min_le_left _ _
  have hy0 : ‖f y‖ ^ 2 = 0 := by
    have hny : y ∉ tsupport f := by
      intro hmem
      have h2 : |y| ≤ R := by simpa [Real.norm_eq_abs] using hR hmem
      have h1 : y ≤ -|R| - 1 := min_le_right _ _
      have h3 : -y ≤ |y| := neg_le_abs _
      have h4 : R ≤ |R| := le_abs_self R
      linarith
    simp [image_eq_zero_of_notMem_tsupport hny]
  have hint : IntervalIntegrable g' volume y x := hgc.intervalIntegrable _ _
  have hftc : ∫ t in y..x, g' t = ‖f x‖ ^ 2 - ‖f y‖ ^ 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => edge_normSq_hasDerivAt f hf t) hint
  have hmono : ∫ t in y..x, g' t ≤ ∫ t in y..x, h t :=
    intervalIntegral.integral_mono_on hyx hint (hhc.intervalIntegrable _ _)
      (fun t _ => edge_re_mul_le (f t) (deriv f t) hδ)
  have hle : ∫ t in y..x, h t ≤ ∫ t, h t := by
    rw [intervalIntegral.integral_of_le hyx]
    exact setIntegral_le_integral hhint (Filter.Eventually.of_forall hhnn)
  rw [hy0, sub_zero] at hftc
  linarith [hftc ▸ hmono]
