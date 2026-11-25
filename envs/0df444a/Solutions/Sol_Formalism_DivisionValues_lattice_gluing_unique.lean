-- Prove2me | solution 1 for Formalism.DivisionValues.lattice_gluing_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:04.847111+00:00
-- url     : https://prove2.me/submissions/06651b04-0f36-4677-b82f-caa89164902d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_lg
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_le_of_forall_localized_le_of_not_isField
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_eq_of_localization_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open GluingInclusion Formalism.HermitianLatticesTheory
namespace Formalism.DivisionValues
theorem _root_.solution : LatticeGlueUnique := by
  intro K _ _ D R R'
  have hR := NumberField.RingOfIntegers.not_isField K
  refine ⟨eq_of_localization_eq R R', le_of_forall_localized_le_of_not_isField hR R R', ?_⟩
  apply le_antisymm
  · intro x hx
    exact lg hR R x fun w => (Submodule.mem_iInf _).1 hx w
  · intro x hx
    exact (Submodule.mem_iInf _).2 fun w => ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩
end Formalism.DivisionValues
