-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:42.017343+00:00
-- url     : https://prove2.me/submissions/7ee945c0-5ccb-4469-a4af-58f552bd5363

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_sum_eq_zero
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_stdPoly_update
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
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
    (E : H →L[ℂ] H) (M : ℕ) (h : ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0) (a : Fin M → H →L[ℂ] H) :
    stdPoly E a = 0 := by
  have key : ∀ (s : Finset (Fin M)) (a : Fin M → H →L[ℂ] H), (∀ i, i ∉ s → ∃ g, σ g = a i) → stdPoly E a = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      choose g hg using fun i => ha i (Finset.notMem_empty i)
      have := h g
      simpa only [hg] using this
    | insert j s hj ih =>
      intro a ha
      obtain ⟨A, B, hAB⟩ := stdPoly_update E a j
      have h0 : ∀ g, stdPoly E (Function.update a j (σ g)) = 0 := by
        intro g
        apply ih
        intro i hi
        by_cases hij : i = j
        · subst hij; exact ⟨g, by simp⟩
        · rw [Function.update_of_ne hij]
          exact ha i (by simp [hij, hi])
      rw [← Function.update_eq_self j a, hAB]
      ext v
      have := sum_eq_zero σ hσ hirr A (fun π => B π v) (fun g => by
        have h1 := congrArg (fun X : H →L[ℂ] H => X v) ((hAB (σ g)).symm.trans (h0 g))
        simpa using h1) (a j)
      simpa using this
  exact key Finset.univ a fun i hi => absurd (Finset.mem_univ i) hi
end CompanionTheory.D.gk.admitted.FinOfPIAux
