-- Prove2me | solution 1 for Formalism.NG.IdempotentCriticalLength.jac_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:16.733893+00:00
-- url     : https://prove2.me/submissions/7fc53df3-9153-4585-a12d-fdc4ce9dcb81

import Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentCriticalLength
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
namespace Formalism.NG.IdempotentCriticalLength
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {a : Λ} (ha : a ∈ Ring.jacobson Λ) (w : V) : a • w = 0 :=
  Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator (R := Λ) (M := V) ha) w
end Formalism.NG.IdempotentCriticalLength
