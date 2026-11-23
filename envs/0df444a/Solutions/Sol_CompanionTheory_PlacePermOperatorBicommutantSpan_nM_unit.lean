-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.nM_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:05.241301+00:00
-- url     : https://prove2.me/submissions/c3b96912-6069-40be-8be6-b6dc200598cb

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hypJ_eq
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hform_eq
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_gram_blk

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
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) {w : Fin M → K} {z : K} (hz : z + s z + hform s J w w = 0) :
    cT s (nM s J w z) * hypJ J * nM s J w z = hypJ J := by
  have e : (s : K → K) ∘ (-((s ∘ w) ᵥ* J)) = -(J *ᵥ w) := by
    funext i
    have : ∀ j, s (J j i) = J i j := fun j => congrFun (congrFun hJ i) j
    simp [vecMul, mulVec, dotProduct, hs, this, mul_comm]
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  rw [hform_eq] at hz
  rw [nM, pm, gram_blk, hypJ_eq, e, z0]
  simp [cT_one, hz]
end CompanionTheory.PlacePermOperatorBicommutantSpan
