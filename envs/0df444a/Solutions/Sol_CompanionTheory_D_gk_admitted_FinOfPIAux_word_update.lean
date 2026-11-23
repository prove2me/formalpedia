-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.word_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:36.646713+00:00
-- url     : https://prove2.me/submissions/f7982c06-808a-4a89-bb73-8cd2a5886c86

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
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
theorem _root_.solution {R : Type*} [Ring R] (E : R) {n : ℕ} (f : Fin n → R) (k : Fin n) :
    ∃ A B : R, ∀ T, word E (List.ofFn (Function.update f k T)) = A * T * B := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · refine ⟨E, word E (List.ofFn fun i => f i.succ), fun T => ?_⟩
      simp [List.ofFn_succ]
    · obtain ⟨A, B, h⟩ := ih (fun i => f i.succ) k
      refine ⟨E * f 0 * A, B, fun T => ?_⟩
      have h1 : (fun i : Fin n => Function.update f k.succ T i.succ) = Function.update (fun i => f i.succ) k T := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · rw [Function.update_of_ne hi, Function.update_of_ne (fun e => hi (Fin.succ_injective _ e))]
      rw [List.ofFn_succ, word_cons, h1, h, Function.update_of_ne (Fin.succ_ne_zero _).symm]
      simp [mul_assoc]
end CompanionTheory.D.gk.admitted.FinOfPIAux
