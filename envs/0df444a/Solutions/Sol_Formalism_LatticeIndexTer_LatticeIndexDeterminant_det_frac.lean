-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.det_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:32.397876+00:00
-- url     : https://prove2.me/submissions/3386078f-9259-4b28-8598-7e1d67efc94a

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet

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
theorem _root_.solution {X Y ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) :
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective O
    (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hb0
  have hdet : (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det ≠ 0 :=
    (LinearEquiv.isUnit_det f bX bY).ne_zero
  refine ⟨a, b, ?_, hb0, ?_⟩
  · rintro rfl
    apply hdet
    rw [← hab, map_zero, zero_div]
  · rw [← hab, div_mul_cancel₀ _ hbK]
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
