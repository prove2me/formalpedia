-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.proj_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:35.355462+00:00
-- url     : https://prove2.me/submissions/b47d6a20-2078-4878-8a73-f84b24be3930

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_inner_left
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply


attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply

set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [CompleteSpace H] [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) [C.HasOrthogonalProjection]
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (g : G) (z : PiLp 2 (fun _ : ι => H)) :
    C.starProjection (diag (σ g) z) = diag (σ g) (C.starProjection z) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hC g _ (C.starProjection_apply_mem z)
  · intro w hw
    rw [← map_sub]
    have h : ⟪diag (σ g) (z - C.starProjection z), w⟫_ℂ = ⟪z - C.starProjection z, diag (σ g⁻¹) w⟫_ℂ := by
      simp only [PiLp.inner_apply, diag_apply, inner_left σ hσ]
    rw [h]
    exact C.starProjection_inner_eq_zero z _ (hC _ _ hw)
end CompanionTheory.D.gk.admitted.FinOfPIAux
