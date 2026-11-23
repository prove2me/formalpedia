-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.hypJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:34.241863+00:00
-- url     : https://prove2.me/submissions/28997009-f222-4307-9b77-bc0068ec507e

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
theorem _root_.solution (J : Matrix (Fin M) (Fin M) K) : hypJ J = blk 0 1 0 1 0 0 0 0 J := rfl
end CompanionTheory.PlacePermOperatorBicommutantSpan
