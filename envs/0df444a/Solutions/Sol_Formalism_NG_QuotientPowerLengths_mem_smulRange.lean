-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.mem_smulRange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:28.25083+00:00
-- url     : https://prove2.me/submissions/852a1af4-115e-4651-9fa8-8bb05a2752a8

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module O M] (l : O) (x : M) :
    x ∈ smulRange M l ↔ ∃ y, l • y = x := by
  first
    | exact Iff.rfl
    | simp [smulRange, LinearMap.mem_range]
end Formalism.NG.QuotientPowerLengths
