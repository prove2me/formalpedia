-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.LatticeLiftIndependence.latWt_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:44.169072+00:00
-- url     : https://prove2.me/submissions/99f61347-3373-498c-8c0f-8a0e0abcdff6

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.LatticeLiftIndependence
open Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.ThetaLiftIndependence.LatticeLiftIndependence
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : latWt h (gmap g M) = latWt h M := by
  unfold latWt
  rw [Nat.card_congr (conjEquiv h hg M)]
end Formalism.ThetaLiftIndependence.LatticeLiftIndependence
