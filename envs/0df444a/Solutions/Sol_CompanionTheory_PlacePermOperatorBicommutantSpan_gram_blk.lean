-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.gram_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:12.420841+00:00
-- url     : https://prove2.me/submissions/ea045241-d6f4-40a1-9182-0f609890f4ab

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_mul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_map
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_block_matrix_transpose
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
theorem _root_.solution (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (a b d : K) (r t w : Fin M → K)
    (U : Matrix (Fin M) (Fin M) K) :
    cT s (blk a b r 0 d t 0 w U) * hypJ J * blk a b r 0 d t 0 w U =
      blk 0 (s a * d) (s a • t) (s d * a) (s d * b + s b * d + ((s ∘ w) ᵥ* J) ⬝ᵥ w)
        (s d • r + s b • t + ((s ∘ w) ᵥ* J) ᵥ* U) (a • (s ∘ t)) (b • (s ∘ t) + d • (s ∘ r) + (cT s U * J) *ᵥ w)
        (vecMulVec (s ∘ t) r + vecMulVec (s ∘ r) t + cT s U * J * U) := by
  have z : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  simp [cT, blk_map, block_matrix_transpose, hypJ_eq, blk_mul, z]
end CompanionTheory.PlacePermOperatorBicommutantSpan
