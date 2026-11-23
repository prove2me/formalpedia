-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.isClosed_capSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:41.048918+00:00
-- url     : https://prove2.me/submissions/7ee41c6f-0209-416d-9e1b-e1490412d13e

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_continuous_eval
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_isClosed_sesqSet
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
variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution : IsClosed (capSet ρ c xs) := by
  simp only [capSet, Cap, Set.ofPred_forall]
  refine (((isClosed_sesqSet.inter ?_).inter ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (Complex.continuous_conj.comp (continuous_eval _ _)) (continuous_eval _ _)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (Complex.continuous_re.comp (continuous_eval _ _))
  · exact isClosed_iInter fun g => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_eval _ _) (continuous_eval _ _)
  · exact isClosed_iInter fun n => isClosed_le
      (continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_re.comp (continuous_eval _ _)))
      continuous_const
end DiscreteGroups.sglob.LConvKM
