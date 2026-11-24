-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.isTorsionFree_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:16.852806+00:00
-- url     : https://prove2.me/submissions/2aa2b436-5bb8-415d-a295-63a7b0b92d36

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution (U : Submodule (FractionRing O) V) : IsTorsionFree O (V ⧸ U) := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : algebraMap O (FractionRing O) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hr.ne_zero
  have hxy' : algebraMap O (FractionRing O) r • x = algebraMap O (FractionRing O) r • y := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hxy
  exact smul_right_injective (V ⧸ U) hr0 hxy'
end Formalism.NG.QuotientPowerLengths
