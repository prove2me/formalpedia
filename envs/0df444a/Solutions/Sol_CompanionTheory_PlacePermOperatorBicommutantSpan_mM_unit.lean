-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.mM_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:32.32193+00:00
-- url     : https://prove2.me/submissions/ec730d50-2cf3-4e8d-8f38-1324b7f3efb0

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hypJ_eq
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
theorem _root_.solution (hs : ∀ x, s (s x) = x) (a : Kˣ) :
    cT s (pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1) * hypJ J * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 = hypJ J := by
  have z0 : (s : K → K) ∘ (0 : Fin M → K) = 0 := funext fun _ => map_zero s
  rw [pm, gram_blk, hypJ_eq, z0]
  simp [cT_one, hs, ← map_mul]
end CompanionTheory.PlacePermOperatorBicommutantSpan
