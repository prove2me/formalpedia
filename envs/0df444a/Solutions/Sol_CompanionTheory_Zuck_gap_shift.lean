-- Prove2me | solution 1 for CompanionTheory.Zuck.gap_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:32:10.449303+00:00
-- url     : https://prove2.me/submissions/1a5fb15f-31df-4fde-a1f5-bd47427d9f9a

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
import Theorems.Thm_CompanionTheory_Zuck_shift_apply
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
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
theorem _root_.solution {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hg : GapAtLeast ε μ h) (b : Bool) (s : Fin n) :
    GapAtLeast ε (shift b μ s) (h - 1) := by
  intro a c hac
  have h1 := hg a c hac
  have hne : a ≠ c := fun e => hac (by rw [e])
  rw [shift_apply, shift_apply]
  rw [le_abs] at h1 ⊢
  by_cases e1 : a = s <;> by_cases e2 : c = s
  · exact absurd (e1.trans e2.symm) hne
  all_goals cases b <;> simp only [e1, e2, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    rcases h1 with h1 | h1 <;> first | (left; linarith) | (right; linarith)
end CompanionTheory.Zuck
