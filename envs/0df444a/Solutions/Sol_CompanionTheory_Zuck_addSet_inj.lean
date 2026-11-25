-- Prove2me | solution 1 for CompanionTheory.Zuck.addSet_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:25.621744+00:00
-- url     : https://prove2.me/submissions/da26ae16-9ef8-46eb-ba77-db8c390863e0

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {n : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution {l : ℕ} (μ : Fin n → ℝ) : Function.Injective fun I : Sub n l => addSet μ I.1 := by
  intro I J h
  refine Subtype.ext (Finset.ext fun a => ?_)
  have := congrFun h a
  simp only [addSet, add_right_inj] at this
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all
end CompanionTheory.Zuck
