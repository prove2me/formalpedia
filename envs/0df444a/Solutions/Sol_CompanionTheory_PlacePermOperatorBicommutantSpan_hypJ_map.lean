-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.hypJ_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:18.25885+00:00
-- url     : https://prove2.me/submissions/73208b68-8cc2-4a25-a6ed-98e03d10f9b9

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_map
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hypJ_eq

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
theorem _root_.solution {L : Type} [CommRing L] (φ : K →+* L) (J : Matrix (Fin M) (Fin M) K) :
    (hypJ J).map φ = hypJ (J.map φ) := by
  simp only [hypJ_eq, blk_map, map_zero, map_one]
  congr 1 <;> exact funext fun _ => map_zero φ
end CompanionTheory.PlacePermOperatorBicommutantSpan
