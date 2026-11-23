-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.block_matrix_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:17.214049+00:00
-- url     : https://prove2.me/submissions/50256a64-eb96-430a-8933-15a44f6d9908

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
theorem _root_.solution (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U)ᵀ = blk a c u b d w r s Uᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl
end CompanionTheory.PlacePermOperatorBicommutantSpan
