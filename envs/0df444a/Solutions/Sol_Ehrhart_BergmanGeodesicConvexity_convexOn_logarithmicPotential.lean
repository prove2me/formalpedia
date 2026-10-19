-- Prove2me | solution 1 for Ehrhart.BergmanGeodesicConvexity.convexOn_logarithmicPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/86f4ce60-9bb2-46b6-be6e-457d18bf0ae1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanGeodesicConvexity_exponentialMoment_sq_le_partition_mul_second
import Theorems.Thm_Ehrhart_BergmanGeodesicConvexity_hasDerivAt_logarithmicSlope

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanGeodesicConvexity
open Set Module
open scoped BigOperators InnerProductSpace
namespace Ehrhart.BergmanGeodesicConvexity
theorem _root_.solution {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {k : ℝ} (hk : 0 < k) :
    ConvexOn ℝ Set.univ (logarithmicPotential w order k) := by
  have hderiv (t : ℝ) :
      deriv (logarithmicPotential w order k) t =
        exponentialMoment w order 1 t /
          exponentialPartition w order t / k :=
    (hasDerivAt_logarithmicPotential w order hw hpositive k t).deriv
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t =>
      (hasDerivAt_logarithmicPotential w order hw hpositive k t).differentiableAt
  · have heq : deriv (logarithmicPotential w order k) =
        fun t : ℝ => exponentialMoment w order 1 t /
          exponentialPartition w order t / k :=
        funext hderiv
    rw [heq]
    exact fun t =>
      (hasDerivAt_logarithmicSlope w order hw hpositive k t).differentiableAt
  · intro t
    change 0 ≤ deriv (deriv (logarithmicPotential w order k)) t
    have heq : deriv (logarithmicPotential w order k) =
        fun q : ℝ => exponentialMoment w order 1 q /
          exponentialPartition w order q / k :=
        funext hderiv
    rw [heq,
      (hasDerivAt_logarithmicSlope w order hw hpositive k t).deriv]
    apply div_nonneg
    · apply div_nonneg
      · have hvar :=
          exponentialMoment_sq_le_partition_mul_second
            w order hw t
        nlinarith
      · exact sq_nonneg _
    · exact hk.le
end Ehrhart.BergmanGeodesicConvexity
