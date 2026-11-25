-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.mem_spanBox_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:31.113724+00:00
-- url     : https://prove2.me/submissions/5995eb5f-7cc1-42af-ae19-2609b932797e

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_kfin_zero
import Theorems.Thm_CompanionTheory_LimBd_Main_mem_box_self
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
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution {μ : Fin (2 * r + k + 1) → ℝ} {φ ψ ψ' : B.Mat k r → ℂ} (hφ : IsCoef k r ε μ φ)
    (hψ' : ψ' ∈ SpanBox k r ε μ 1) (h : ∀ g ∈ B.GV k r, ψ g = ψ' g) : ψ ∈ SpanBox k r ε μ 1 := by
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, hw, -⟩ := hφ
  have h0 : ψ - ψ' ∈ SpanBox k r ε μ 1 := Submodule.subset_span ⟨μ, mem_box_self μ, H, i1, i2, i3, σ, 0, w, hμ, hσ,
    kfin_zero σ, hw, fun g hg => by simp [h g hg]⟩
  simpa using Submodule.add_mem _ h0 hψ'
end CompanionTheory.LimBd.Main
