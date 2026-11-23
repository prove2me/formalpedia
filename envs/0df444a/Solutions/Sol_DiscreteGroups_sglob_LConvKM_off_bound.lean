-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.off_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:44.488849+00:00
-- url     : https://prove2.me/submissions/7ae993b9-68bf-492a-b943-d18a752cb229

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_norm_le_polar
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_diag_bound
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
theorem _root_.solution (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x y : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, ‖F x y‖ ≤ R := by
  obtain ⟨R₁, h₁⟩ := diag_bound ρ c xs hsp hc (x + y)
  obtain ⟨R₂, h₂⟩ := diag_bound ρ c xs hsp hc (x - y)
  obtain ⟨R₃, h₃⟩ := diag_bound ρ c xs hsp hc (x + Complex.I • y)
  obtain ⟨R₄, h₄⟩ := diag_bound ρ c xs hsp hc (x - Complex.I • y)
  refine ⟨(R₁ + R₂ + R₃ + R₄) / 4, fun F hF => ?_⟩
  have := norm_le_polar (mkForm F hF.1.1.1.1) hF.1.1.1.2 hF.1.1.2 x y
  simp only [mkForm_apply] at this
  linarith [h₁ F hF, h₂ F hF, h₃ F hF, h₄ F hF]
end DiscreteGroups.sglob.LConvKM
