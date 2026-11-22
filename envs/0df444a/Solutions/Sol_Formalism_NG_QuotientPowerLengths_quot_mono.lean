-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.quot_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:52.093678+00:00
-- url     : https://prove2.me/submissions/9a4d62af-5458-48b8-899d-da534f3b0cf8

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
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module O M] {A B : Submodule O M} (h : A ≤ B) :
    Module.length O (M ⧸ B) ≤ Module.length O (M ⧸ A) := by
  exact Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)
end Formalism.NG.QuotientPowerLengths
