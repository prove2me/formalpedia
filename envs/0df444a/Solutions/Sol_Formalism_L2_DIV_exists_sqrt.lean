-- Prove2me | solution 1 for Formalism.L2.DIV.exists_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:44.955539+00:00
-- url     : https://prove2.me/submissions/87e3f04b-2c70-4f87-b508-24848245dea5

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (m : ℤ) : ∃ x : Qb, x ∈ sqrts m := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)
  exact ⟨x, hx⟩
end Formalism.L2.DIV
