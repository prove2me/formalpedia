-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.index_scalar_multiple_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:40.558744+00:00
-- url     : https://prove2.me/submissions/598fe2be-c4dd-44a6-9782-c488d15dff40

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_idxDet_core

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
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution {X ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module K X]
    [Module O X] [IsScalarTower O K X] (bN : Basis ι K X) (u : K) (hu : u ≠ 0) (a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : algebraMap O K a = u ^ Fintype.card ι * algebraMap O K b) :
    idx O X (Submodule.span O (Set.range bN))
        ((Submodule.span O (Set.range bN)).map ((u • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
      ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
        ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) := by
  let f : X ≃ₗ[K] X := LinearEquiv.smulOfNeZero K X u hu
  have hf : (f : X →ₗ[K] X) = u • LinearMap.id := by
    ext x
    rfl
  have hdet : (LinearMap.toMatrix bN bN (f : X →ₗ[K] X)).det = u ^ Fintype.card ι := by
    rw [hf, map_smul, LinearMap.toMatrix_id, Matrix.det_smul, Matrix.det_one, mul_one]
  rw [← hf]
  exact idxDet_core bN bN f a b ha hb (by rw [hdet]; exact h)
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
