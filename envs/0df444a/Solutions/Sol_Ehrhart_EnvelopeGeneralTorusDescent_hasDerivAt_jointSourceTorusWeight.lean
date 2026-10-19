-- Prove2me | solution 1 for Ehrhart.EnvelopeGeneralTorusDescent.hasDerivAt_jointSourceTorusWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/efe1cccf-6128-44b8-9ab3-6758db49160b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeTorusDescent_hasDerivAt_sourceJointTimeEmbedding
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_jointSourceTorusVelocity_eq_cover

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.EnvelopeGeneralTorusDescent
open Set Function Filter MeasureTheory
open ComplexKillingSaturationBridge MatrixTorusBochnerIdentity JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative EnvelopeSmoothing EnvelopeTorusDescent
open scoped Topology ContDiff
namespace Ehrhart.EnvelopeGeneralTorusDescent
theorem _root_.solution {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    HasDerivAt (fun s : ℝ => jointSourceTorusWeight F s q)
      (jointSourceTorusVelocity F t q) t := by
  have heq :
      (fun s : ℝ => jointSourceTorusWeight F s q) =
      (fun s : ℝ =>
        F (sourceJointTimeEmbedding (sourceTorusCoverPoint q) s)) := by
    funext s
    exact jointSourceTorusWeight_eq_cover F s q
  rw [heq, jointSourceTorusVelocity_eq_cover]
  exact (hF.differentiable (by norm_num)
    (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)).hasFDerivAt
      |>.comp_hasDerivAt t
        (hasDerivAt_sourceJointTimeEmbedding
          (sourceTorusCoverPoint q) t)
end Ehrhart.EnvelopeGeneralTorusDescent
