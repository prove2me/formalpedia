-- Prove2me | solution 1 for Ehrhart.BergmanJetBergmanProbabilityTransfer.momentTorusBergmanProbability_eq_base_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/8a5df7df-b829-4045-8231-53e1f5f06a23

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_continuous_momentDiagonalKernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBergmanProbabilityTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanMonomials BergmanNormalization
open JetEnvelopeSlopeConvergence LogPartitionConvexity MomentOptimizer MomentWeakFirstVariation
open MomentRegularity MomentWeakBergman MomentWeakBergmanProbabilityEndpoint
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBergmanProbabilityTransfer
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K) :
    momentTorusBergmanProbability K F k =
      (sourceTorusBaseMeasure n).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal (momentWeakTorusBergmanDensity K F k q)) := by
  let base : Measure (LogTorus n) := sourceTorusBaseMeasure n
  let w : LogTorus n → ℝ≥0∞ :=
    fun q => radialWeight k (momentNormalizedPotential F) q.1
  let d : LogTorus n → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (diagonalKernel K k (momentNormalizedPotential F) q.1 /
        (bergmanDimension K k : ℝ))
  have hwmeas : Measurable w :=
    (radialWeight_measurable k
      (continuous_momentNormalizedPotential F)).comp measurable_fst
  have hdmeas : Measurable d :=
    ENNReal.measurable_ofReal.comp
      (((continuous_momentDiagonalKernel K hk F).div_const
        (bergmanDimension K k : ℝ)).comp continuous_fst).measurable
  have hweight :
      weightedTorusMeasure k (momentNormalizedPotential F) =
        base.withDensity w := by
    simpa [base, w, sourceTorusBaseMeasure] using
      weightedTorusMeasure_eq_withDensity k
        (continuous_momentNormalizedPotential F)
  change
    (weightedTorusMeasure k
      (momentNormalizedPotential F)).withDensity d =
      base.withDensity
        (fun q => ENNReal.ofReal
          (momentWeakTorusBergmanDensity K F k q))
  rw [hweight, ← MeasureTheory.withDensity_mul base hwmeas hdmeas]
  congr 1
  funext q
  dsimp [w, d]
  unfold radialWeight momentWeakTorusBergmanDensity
    normalizedDiagonalDensity
  rw [weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel K hk]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring
end Ehrhart.BergmanJetBergmanProbabilityTransfer
