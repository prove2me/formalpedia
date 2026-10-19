-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integrable_angularHolomorphicPartitionDerivativeLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/1578fcc5-9148-4dd5-90a7-1970b0df1b70

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_coverAngularSmoothPartition
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularSourceAngularDerivativeLift

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
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (j : Fin n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            f (complexTorusCoverProjection n z))
      (coverWeightedMeasure (angularCoverPotential a)) := by
  let μ : Measure (TorusCharacters.LogSpace n) :=
    coverWeightedMeasure (angularCoverPotential a)
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  let d₀ := sourceAngularDerivativeLift f v₀
  let d₁ := sourceAngularDerivativeLift f v₁
  have hi₀ : Integrable d₀ μ :=
    integrable_angularSourceAngularDerivativeLift ha hf hfc v₀
  have hi₁ : Integrable d₁ μ :=
    integrable_angularSourceAngularDerivativeLift ha hf hfc v₁
  have hcomb : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (d₀ z - Complex.I * d₁ z) / 2) μ :=
    (hi₀.sub (hi₁.const_mul Complex.I)).div_const 2
  have hη : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp)
  apply hcomb.congr
  filter_upwards [] with z
  unfold holomorphicCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hη z v₀,
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hη z v₁]
  dsimp [d₀, d₁, sourceAngularDerivativeLift]
  ring
end Ehrhart.WeightedTorusBochner
