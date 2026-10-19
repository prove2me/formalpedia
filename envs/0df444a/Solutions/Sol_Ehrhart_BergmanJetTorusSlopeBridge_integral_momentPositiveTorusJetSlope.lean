-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeBridge.integral_momentPositiveTorusJetSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/ecb18968-2ffc-4fca-952d-53a27bdf50db

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_integral_momentTorusTruncatedJetOrderDensity
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_continuous_momentDiagonalKernel
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_momentTorusNormalizedDensity_mul_positiveJetSlope

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusSlopeBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open TorusCharacters WeightedTorusHilbert BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge JetEnvelopeRightDerivative
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetTorusSlopeBridge
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) :
    (∫ q : LogTorus n,
      momentPositiveTorusJetSlope K hk F htransport p N q
        ∂(momentTorusBergmanProbability K F k)) =
      (∑ i : Fin (bergmanDimension K k),
        (momentTruncatedJetOrder
          K hk F htransport p N i : ℝ)) /
        ((k : ℝ) * (bergmanDimension K k : ℝ)) := by
  let d : LogTorus n → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (diagonalKernel K k (momentNormalizedPotential F) q.1 /
        (bergmanDimension K k : ℝ))
  have hdmeas : Measurable d :=
    ENNReal.measurable_ofReal.comp
      (((continuous_momentDiagonalKernel K hk F).div_const
        (bergmanDimension K k : ℝ)).comp
          continuous_fst).measurable
  have hfinite :
      ∀ᵐ q ∂(weightedTorusMeasure k (momentNormalizedPotential F)),
        d q < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold momentTorusBergmanProbability
  rw [integral_withDensity_eq_integral_toReal_smul hdmeas hfinite]
  have hdim : 0 < (bergmanDimension K k : ℝ) := by
    exact_mod_cast bergmanDimension_pos K hk
  change
    (∫ q : LogTorus n,
      (ENNReal.ofReal
        (diagonalKernel K k (momentNormalizedPotential F) q.1 /
          (bergmanDimension K k : ℝ))).toReal *
        momentPositiveTorusJetSlope K hk F htransport p N q
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) = _
  simp_rw [ENNReal.toReal_ofReal
    (div_nonneg
      (diagonalKernel_momentNormalized_pos
        K hk F htransport _).le hdim.le),
    momentTorusNormalizedDensity_mul_positiveJetSlope
      K hk F htransport p N]
  rw [MeasureTheory.integral_div,
    integral_momentTorusTruncatedJetOrderDensity
      K hk F htransport p N]
end Ehrhart.BergmanJetTorusSlopeBridge
