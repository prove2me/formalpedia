-- Prove2me | solution 1 for Ehrhart.TorusWeightedCoverGlobalGreen.locallyIntegrable_complex_inner_mul_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/d1cf2b5e-1320-438f-8592-47c4c916bf69

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedCoverGlobalGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusWeightedCoverGlobalGreen
theorem _root_.solution
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [T2Space E]
    {μ : Measure E} {F G : E → ℂ}
    (hF : LocallyIntegrable F μ)
    (hG : Continuous G)
    (hGcompact : HasCompactSupport G) :
    Integrable (fun z => @inner ℂ ℂ _ (F z) (G z)) μ := by
  have hconjcontinuous : Continuous (fun z => conj (G z)) :=
    Complex.continuous_conj.comp hG
  have hconjcompact : HasCompactSupport (fun z => conj (G z)) := by
    simpa [Function.comp_def] using
      hGcompact.comp_left (g := (starRingEnd ℂ)) (map_zero _)
  have hmul : Integrable (fun z => F z * conj (G z)) μ := by
    simpa [smul_eq_mul] using
      hF.integrable_smul_right_of_hasCompactSupport
        hconjcontinuous hconjcompact
  have hc := Complex.conjCLE.toContinuousLinearMap.integrable_comp hmul
  simpa [RCLike.inner_apply', map_mul, mul_comm] using hc
end Ehrhart.TorusWeightedCoverGlobalGreen
