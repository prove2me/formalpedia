-- Prove2me | solution 1 for CompanionTheory.Zuck.casG_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:28.550224+00:00
-- url     : https://prove2.me/submissions/6c34e143-035c-4a5e-808c-5cb1f2735420

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
import Theorems.Thm_CompanionTheory_Zuck_shift_apply
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
theorem _root_.solution (b : Bool) (μ : Fin n → ℝ) (s : Fin n) :
    casG (shift b μ s) = casG μ + 2 * (if b then -1 else 1) * μ s + 1 := by
  have : ∑ a, shift b μ s a ^ 2 = ∑ a, (μ a ^ 2 + if a = s then 2 * (if b then -1 else 1) * μ s + 1 else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [shift_apply]
    by_cases h : a = s
    · subst h; cases b <;> simp <;> ring
    · simp [h]
  unfold casG
  rw [this, Finset.sum_add_distrib]
  simp
  ring
end CompanionTheory.Zuck
