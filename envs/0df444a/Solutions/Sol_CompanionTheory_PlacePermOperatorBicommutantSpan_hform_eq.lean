-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.hform_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:33.606333+00:00
-- url     : https://prove2.me/submissions/0164034f-6e24-4217-bb9c-fcba6d632aca

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J x y = ((s ∘ x) ᵥ* J) ⬝ᵥ y := by
  simp only [hform, vecMul, dotProduct, Finset.sum_mul, Function.comp]
  exact Finset.sum_comm
end CompanionTheory.PlacePermOperatorBicommutantSpan
