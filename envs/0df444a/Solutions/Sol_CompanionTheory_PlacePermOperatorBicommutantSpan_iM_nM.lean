-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.iM_nM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:18.996801+00:00
-- url     : https://prove2.me/submissions/68e0b8eb-c059-4210-bebb-ec98eda71d01

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_pm_mul

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
theorem _root_.solution {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) (w : Fin M → K) (z : K) :
    pm 1 0 0 1 0 U * nM s J w z = nM s J (U *ᵥ w) z * pm 1 0 0 1 0 U := by
  have e : (s : K → K) ∘ (U *ᵥ w) = (s ∘ w) ᵥ* cT s U := by
    funext i; simp [vecMul, mulVec, dotProduct, cT, mul_comm]
  simp [nM, pm_mul, e, neg_vecMul, hU]
end CompanionTheory.PlacePermOperatorBicommutantSpan
