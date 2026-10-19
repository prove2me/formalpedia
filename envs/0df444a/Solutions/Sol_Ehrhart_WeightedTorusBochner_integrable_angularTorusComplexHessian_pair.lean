-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integrable_angularTorusComplexHessian_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/679d3192-6774-4f23-ac77-c500367f2d00

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBochner
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    Integrable
      (fun p : LogTorus n =>
        (torusScalarRepresentative F p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative G p))
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have hFc := continuous_torusScalarRepresentative_of_periodic
    hF.continuous hFp
  have hGc' := continuous_torusScalarRepresentative_of_periodic
    hG.continuous hGp
  apply ((hFc.mul (continuous_angularTorusComplexHessian ha2 i j)).mul
    (Complex.continuous_conj.comp hGc')).integrable_of_hasCompactSupport
  exact (hasCompactSupport_sourceTorusConj hGc).mul_left
end Ehrhart.WeightedTorusBochner
