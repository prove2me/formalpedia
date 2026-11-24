-- Prove2me | solution 1 for Formalism.REAL.factorAction_mul_pointwiseAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:35:01.935588+00:00
-- url     : https://prove2.me/submissions/8cd0898f-0b91-49ac-bdd8-b8a7c8a6e550

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext
import Theorems.Thm_Formalism_REAL_factorAction_apply
import Theorems.Thm_Formalism_REAL_pointwiseAction_apply

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) (a b c d : Fin n) :
    factorAction (V := V) i a b * ptE (j := j) E c d = ptE E c d * factorAction i a b := by
  refine LinearMap.ext fun F => indexArray_ext fun α => ?_
  change factorAction i a b (ptE E c d F) α = ptE E c d (factorAction i a b F) α
  simp only [factorAction_apply, pointwiseAction_apply]
  split_ifs <;> simp
end Formalism.REAL
