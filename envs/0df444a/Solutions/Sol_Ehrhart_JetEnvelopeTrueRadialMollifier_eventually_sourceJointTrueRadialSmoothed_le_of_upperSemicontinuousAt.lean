-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/2ecfd885-aa24-4907-afb5-7536bbbee4c3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_tendsto_sourceJointTrueRadialRadius

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
attribute [local instance] Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.JetEnvelopeTrueRadialMollifier
theorem _root_.solution
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (q : SourceJointComplexCover n)
    (hupper : UpperSemicontinuousAt f q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      sourceJointTrueRadialSmoothed f k q ≤ f q + ε := by
  have hnear : ∀ᶠ z : SourceJointComplexCover n in 𝓝 q,
      f z < f q + ε :=
    hupper (f q + ε) (lt_add_of_pos_right _ hε)
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp hnear
  have hradius :
      ∀ᶠ k : ℕ in atTop,
        1 / ((k + 1 : ℕ) : ℝ) < δ :=
    tendsto_sourceJointTrueRadialRadius (Iio_mem_nhds hδ)
  filter_upwards [hradius] with k hk
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y * f (q - y)
      ∂(volume : Measure (SourceJointComplexCover n))) ≤
        ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y * (f q + ε)
          ∂(volume : Measure (SourceJointComplexCover n)) := by
      apply MeasureTheory.integral_mono
        (integrable_sourceJointTrueRadialMollifier_mul_translate
          hf k q)
        ((integrable_sourceJointTrueRadialMollifier n k).mul_const
          (f q + ε))
      intro y
      by_cases hy : sourceJointTrueRadialMollifier n k y = 0
      · simp [hy]
      · have hball :=
          support_sourceJointTrueRadialMollifier_subset_closedBall k hy
        have hnorm : ‖y‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hball
        have hdist : dist (q - y) q < δ := by
          have hsmall := hnorm.trans_lt hk
          simpa [dist_eq_norm, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm] using hsmall
        exact mul_le_mul_of_nonneg_left
          (hlocal hdist).le
          (sourceJointTrueRadialMollifier_nonneg n k y)
    _ = f q + ε := by
      rw [MeasureTheory.integral_mul_const,
        integral_sourceJointTrueRadialMollifier, one_mul]
end Ehrhart.JetEnvelopeTrueRadialMollifier
