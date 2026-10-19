-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentHolomorphicRepresentative_schwarz_of_mem_jetFiltration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/9858d0f5-6b0a-434c-9636-075815cd5793

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration

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
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (j : ℕ)
    (hs : s ∈ momentJetFiltration K hk F htransport p j)
    (R B : ℝ)
    (hbound : ∀ z ∈ Metric.ball p R,
      ‖momentHolomorphicRepresentative
        K hk F htransport s z‖ ≤ B)
    (z : TorusCharacters.LogSpace n)
    (hz : z ∈ Metric.ball p R) :
    ‖momentHolomorphicRepresentative K hk F htransport s z‖ ≤
      B * (dist z p / R) ^ j := by
  let f : TorusCharacters.LogSpace n → ℂ :=
    momentHolomorphicRepresentative K hk F htransport s
  cases j with
  | zero =>
      simpa [f] using hbound z hz
  | succ j =>
      have hmemone : s ∈ momentJetFiltration
          K hk F htransport p 1 :=
        momentJetFiltration_antitone K hk F htransport p
          (show 1 ≤ j + 1 by omega) hs
      have hderzero :=
        moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
          K hk F htransport p s 0 hmemone
      have hfzero : f p = 0 := by
        apply norm_eq_zero.mp
        have hn := congrArg norm hderzero
        simpa [f, norm_iteratedFDeriv_zero] using hn
      have hmaps : Set.MapsTo f (Metric.ball p R)
          (Metric.closedBall (f p) B) := by
        intro w hw
        rw [Metric.mem_closedBall, hfzero, dist_zero_right]
        exact hbound w hw
      have hsmall :
          (fun w : TorusCharacters.LogSpace n => f w - f p)
            =o[𝓝 p]
              (fun w : TorusCharacters.LogSpace n =>
                ‖w - p‖ ^ j) :=
        momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
          K hk F htransport p s j hs
      have hd : DifferentiableOn ℂ f (Metric.ball p R) :=
        (differentiable_momentHolomorphicRepresentative
          K hk F htransport s).differentiableOn
      have hsch :=
        Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
          hd hmaps hsmall hz
      simpa [f, hfzero] using hsch
end Ehrhart.BergmanJetLocalGrowth
