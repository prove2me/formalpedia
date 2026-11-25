-- Prove2me | solution 1 for CompanionTheory.Zuck.cas_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:31.549127+00:00
-- url     : https://prove2.me/submissions/4cced84f-dfeb-4dc8-9f33-100582663faa

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
import Theorems.Thm_CompanionTheory_Zuck_shift_apply
import Theorems.Thm_CompanionTheory_Zuck_casG_shift
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
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
theorem _root_.solution {μ : Fin n → ℝ} (hμ : StrictAnti μ) (b : Bool) (s t : Fin n) :
    (casG (shift b (shift b μ s) t) : ℂ) ≠ 2 * (casG (shift b μ s) : ℂ) - (casG μ : ℂ) := by
  intro h
  have h' : casG (shift b (shift b μ s) t) = 2 * casG (shift b μ s) - casG μ := by exact_mod_cast h
  rw [casG_shift b (shift b μ s) t, casG_shift b μ s, shift_apply] at h'
  by_cases e : t = s
  · subst e
    cases b <;> simp at h' <;> linarith
  · apply e
    apply hμ.injective
    cases b <;> simp [e] at h' <;> linarith
end CompanionTheory.Zuck
