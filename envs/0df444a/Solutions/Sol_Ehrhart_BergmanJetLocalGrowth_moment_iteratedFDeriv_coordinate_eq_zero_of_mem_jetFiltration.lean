-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/78212db1-47e5-468f-a492-4493237faedd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_LaurentJetMultiplicityBridge_exists_multiIndexCoordinate_perm
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentHolomorphicJetMap_apply_eq_iteratedFDeriv
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentHolomorphicRepresentative_iteratedFDeriv_comp_perm

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
    {n k r : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (q : Fin r → Fin n) (α : Fin n → ℕ)
    (hdegree : (∑ i, α i) = r)
    (hcount : ∀ i : Fin n,
      Fintype.card {a : Fin r // q a = i} = α i)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (r + 1)) :
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p)
      (fun a => Pi.single (q a) (1 : ℂ)) = 0 := by
  classical
  subst r
  obtain ⟨σ, hσ⟩ := exists_multiIndexCoordinate_perm α q hcount
  let β : JetCounting.JetIndexLT n ((∑ i, α i) + 1) :=
    ⟨α, Nat.lt_succ_self _⟩
  change momentHolomorphicJetMap
    K hk F htransport p ((∑ i, α i) + 1) s = 0 at hs
  have hcanonical :
      (iteratedFDeriv ℂ (∑ i, α i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
        (fun a => Pi.single (multiIndexCoordinate α a) (1 : ℂ)) = 0 := by
    calc
      (iteratedFDeriv ℂ (∑ i, α i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
          (fun a => Pi.single (multiIndexCoordinate α a) (1 : ℂ)) =
        momentHolomorphicJetMap
          K hk F htransport p ((∑ i, α i) + 1) s β :=
          (momentHolomorphicJetMap_apply_eq_iteratedFDeriv
            K hk F htransport p ((∑ i, α i) + 1) s β).symm
      _ = 0 := congrFun hs β
  calc
    (iteratedFDeriv ℂ (∑ i, α i)
      (momentHolomorphicRepresentative K hk F htransport s) p)
        (fun a => Pi.single (q a) (1 : ℂ)) =
      (iteratedFDeriv ℂ (∑ i, α i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
          ((fun a => Pi.single (multiIndexCoordinate α a)
            (1 : ℂ)) ∘ σ) := by
              congr 1
              funext a
              simpa only [Function.comp_apply] using
                congrArg (fun i : Fin n => Pi.single i (1 : ℂ)) (hσ a)
    _ = (iteratedFDeriv ℂ (∑ i, α i)
      (momentHolomorphicRepresentative K hk F htransport s) p)
        (fun a => Pi.single (multiIndexCoordinate α a) (1 : ℂ)) :=
          momentHolomorphicRepresentative_iteratedFDeriv_comp_perm
            K hk F htransport p s _ σ
    _ = 0 := hcanonical
end Ehrhart.BergmanJetLocalGrowth
