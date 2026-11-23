-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.isClosed_sesqSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.934354+00:00
-- url     : https://prove2.me/submissions/5caf0100-ee02-474c-9bfe-dcd96c18f15e

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_continuous_eval
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] DiscreteGroups.sglob.LConvKM.mkForm_apply

set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution : IsClosed (sesqSet : Set (M → M → ℂ)) := by
  simp only [sesqSet, Set.ofPred_forall]
  refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))
  · exact isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))
  · exact isClosed_iInter fun a => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))
end DiscreteGroups.sglob.LConvKM
