-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.pm_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:02.718036+00:00
-- url     : https://prove2.me/submissions/8c21010e-20ae-4f34-a7c8-15966b25d124

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_map

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
theorem _root_.solution {L : Type} [CommRing L] (φ : K →+* L) (a b d : K) (r w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (pm a b r d w U).map φ = pm (φ a) (φ b) (φ ∘ r) (φ d) (φ ∘ w) (U.map φ) := by
  simp only [pm, blk_map, map_zero]
  congr 1 <;> exact funext fun _ => map_zero φ
end CompanionTheory.PlacePermOperatorBicommutantSpan
