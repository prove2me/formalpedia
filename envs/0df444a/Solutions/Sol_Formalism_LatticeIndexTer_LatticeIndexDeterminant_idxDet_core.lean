-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.idxDet_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:20.157671+00:00
-- url     : https://prove2.me/submissions/fbb1cee6-1ddd-4d7c-b661-ba5aea0f459c

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_idx_two_bases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution {X : Type} [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b) :
    idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) := by
  have hmap : (Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O) =
      Submodule.span O (Set.range (bX.map f)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
  have hmat : LinearMap.toMatrix bX bY (f : X →ₗ[K] Y) = bY.toMatrix (bX.map f) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, Basis.map_apply]
  rw [hmap]
  rw [hmat] at h
  exact idx_two_bases bY (bX.map f) a b ha hb h
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
