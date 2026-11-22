-- Prove2me | solution 1 for Formalism.REAL.factorAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:42.359983+00:00
-- url     : https://prove2.me/submissions/c1ed1bca-56a9-4f60-9f76-9bc6cbe4f5e3

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by
  unfold factorAction
  by_cases h1 : (α i).1 = c <;> by_cases h2 : (α i).2 = d <;> simp [h1, h2, arrTo, arrOf]
end Formalism.REAL
