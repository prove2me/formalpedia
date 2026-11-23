-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.isCompact_capSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:55.827023+00:00
-- url     : https://prove2.me/submissions/bcd0ba5b-41ae-4188-bea2-e8e11e722c49

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_isClosed_capSet
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_off_bound
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
theorem _root_.solution (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) :
    IsCompact (capSet ρ c xs) := by
  choose R hR using off_bound ρ c xs hsp hc
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun x => isCompact_univ_pi fun y => isCompact_closedBall (0 : ℂ) (R x y))
    (isClosed_capSet ρ c xs) fun F hF => ?_
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  exact fun x y => hR x y F hF
end DiscreteGroups.sglob.LConvKM
