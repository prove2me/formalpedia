-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.427349+00:00
-- url     : https://prove2.me/submissions/685bd2a4-594d-467c-9283-57c6fd0d8a38

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_schur
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_sum_incl
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_incl
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_proj_comm
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
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) (hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))))
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (T : H →L[ℂ] H) (z : PiLp 2 (fun _ : ι => H)) (hz : z ∈ C) :
    diag T z ∈ C := by
  have : CompleteSpace C := hcl.completeSpace_coe
  have hs : ∀ i j : ι, ∃ c : ℂ, ∀ v, C.starProjection (incl j v) i = c • v := by
    intro i j
    refine schur σ hσ hirr ((PiLp.proj 2 (fun _ : ι => H) i).comp (C.starProjection.comp (incl j))) ?_
    intro g v
    show C.starProjection (incl j (σ g v)) i = σ g (C.starProjection (incl j v) i)
    rw [← diag_incl, proj_comm σ hσ C hC, diag_apply]
  choose c hc using hs
  have hQ : ∀ (w : PiLp 2 (fun _ : ι => H)) (i : ι), C.starProjection w i = ∑ j, c i j • w j := by
    intro w i
    conv_lhs => rw [← sum_incl w, map_sum]
    simp [hc]
  have h1 : C.starProjection z = z := Submodule.starProjection_eq_self_iff.mpr hz
  have h2 : C.starProjection (diag T z) = diag T z := by
    ext i
    rw [hQ, diag_apply, ← h1, hQ, h1]
    simp
  exact Submodule.starProjection_eq_self_iff.mp h2
end CompanionTheory.D.gk.admitted.FinOfPIAux
