-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentHolomorphicJetMap_apply_eq_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/ec3115b2-5e21-4bf0-9b15-d1b751b60546

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_LaurentJetSeparatedness_analyticAt_normalizedHolomorphicMonomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalGrowth
open Set Function Filter MeasureTheory Module Metric Asymptotics
open BergmanMonomials BergmanDiagonalBasisIndependence GlobalBergmanKernelBound AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge
open BergmanJetRealGeodesic JetEnvelopeLocalGrowth LaurentJetMultiplicityBridge
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.BergmanJetLocalGrowth
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ)
    (s : momentMonomialSpan K hk F htransport)
    (α : JetCounting.JetIndexLT n j) :
    momentHolomorphicJetMap K hk F htransport p j s α =
      (iteratedFDeriv ℂ (∑ i, α.val i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
          (fun q => Pi.single
            (multiIndexCoordinate α.val q) (1 : ℂ)) := by
  classical
  unfold momentHolomorphicJetMap
    momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  change
    (∑ u ∈ ((momentLatticeMonomialBasis
        K hk F htransport).repr s).support,
      ((momentLatticeMonomialBasis
        K hk F htransport).repr s u) •
        holomorphicMonomialJet K hk
          (momentNormalizedPotential F) p u α.val) =
      (iteratedFDeriv ℂ (∑ i, α.val i)
        (∑ u ∈ ((momentLatticeMonomialBasis
            K hk F htransport).repr s).support,
          ((momentLatticeMonomialBasis
            K hk F htransport).repr s u) •
            normalizedHolomorphicMonomial K hk
              (momentNormalizedPotential F) u) p)
        (fun q => Pi.single (multiIndexCoordinate α.val q) (1 : ℂ))
  have hderiv :
      iteratedFDeriv ℂ (∑ i, α.val i)
        (∑ u ∈ ((momentLatticeMonomialBasis
            K hk F htransport).repr s).support,
          ((momentLatticeMonomialBasis
            K hk F htransport).repr s u) •
            normalizedHolomorphicMonomial K hk
              (momentNormalizedPotential F) u) p =
        ∑ u ∈ ((momentLatticeMonomialBasis
            K hk F htransport).repr s).support,
          iteratedFDeriv ℂ (∑ i, α.val i)
            (((momentLatticeMonomialBasis
              K hk F htransport).repr s u) •
              normalizedHolomorphicMonomial K hk
                (momentNormalizedPotential F) u) p := by
    apply iteratedFDeriv_sum_apply
    intro u _
    exact
      (LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
        K hk (momentNormalizedPotential F) u p).contDiffAt.const_smul
          ((momentLatticeMonomialBasis
            K hk F htransport).repr s u)
  rw [hderiv]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [iteratedFDeriv_const_smul_apply
    (LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
      K hk (momentNormalizedPotential F) u p).contDiffAt]
  simp [holomorphicMonomialJet]
end Ehrhart.BergmanJetLocalGrowth
