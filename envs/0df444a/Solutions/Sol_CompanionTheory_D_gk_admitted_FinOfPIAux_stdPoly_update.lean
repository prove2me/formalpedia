-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:49.673797+00:00
-- url     : https://prove2.me/submissions/19ed6601-5218-4a73-b6fd-a5f7567f034b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_word_update
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
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
theorem _root_.solution {R : Type*} [Ring R] (E : R) {M : ℕ} (a : Fin M → R) (j : Fin M) :
    ∃ A B : Equiv.Perm (Fin M) → R, ∀ T, stdPoly E (Function.update a j T) = ∑ π, A π * T * B π := by
  have h : ∀ π : Equiv.Perm (Fin M), ∃ A B : R, ∀ T,
      word E (List.ofFn fun i => Function.update a j T (π i)) = A * T * B := by
    intro π
    obtain ⟨A, B, h⟩ := word_update E (fun i => a (π i)) (π.symm j)
    refine ⟨A, B, fun T => ?_⟩
    rw [← h]
    congr 2
    funext i
    by_cases hi : i = π.symm j
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (fun e => hi (by rw [← e]; simp))]
  choose A B h using h
  refine ⟨fun π => ((Equiv.Perm.sign π : ℤ) : R) * A π, B, fun T => ?_⟩
  simp only [stdPoly, h, mul_assoc]
end CompanionTheory.D.gk.admitted.FinOfPIAux
