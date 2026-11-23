-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.eig_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:18.134526+00:00
-- url     : https://prove2.me/submissions/695842f2-22b0-4047-b09a-c595ec24caeb

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (A : FI E) (s : ℕ) : eig E A (s + 2) = eig E A s := by
  ext t
  rw [mem_eig, mem_eig, pow_add]
  simp
end Formalism.FourierDecayAlt.P.S6x3
