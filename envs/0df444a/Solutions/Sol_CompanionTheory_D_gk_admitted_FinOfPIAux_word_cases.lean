-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.word_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:36.327861+00:00
-- url     : https://prove2.me/submissions/d3bd4499-1eef-4b07-b464-5ccf91e48504

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_P2M_CompanionTheory_D_gk_admitted_FinOfPIAux_word_range__04080a514807
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
variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)
omit [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) (l : List ℕ)
    (hl : ∀ a ∈ l, a < M) :
    word E (l.map fun a => (φ (a + 1)).smulRight (x a)) (x M) = 0 ∨
      ∃ k, k + l.length = M ∧ l = List.range' k l.length := by
  induction l with
  | nil => exact Or.inr ⟨M, rfl, rfl⟩
  | cons a l ih =>
    have ha : a < M := hl a (by simp)
    rw [List.map_cons, word_cons, mul_apply_eq_comp, mul_apply_eq_comp]
    rcases ih (fun b hb => hl b (by simp [hb])) with h | ⟨k, hk, h⟩
    · left; rw [h]; simp
    · by_cases hak : a + 1 = k
      · right
        refine ⟨a, by simp; omega, ?_⟩
        rw [List.length_cons, List.range'_succ, hak, ← h]
      · left
        rw [h, word_range' E M φ x hφ _ k hk, ContinuousLinearMap.smulRight_apply, hφ _ (by omega) _ (by omega),
          if_neg hak]
        simp
end CompanionTheory.D.gk.admitted.FinOfPIAux
