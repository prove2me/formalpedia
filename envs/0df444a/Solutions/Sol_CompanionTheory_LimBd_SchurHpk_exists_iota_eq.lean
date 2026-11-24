-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.exists_iota_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:54.938679+00:00
-- url     : https://prove2.me/submissions/905b9523-fcfd-44d1-84ef-021e1f26822b

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_forth_mem
import Theorems.Thm_Formalism_REAL_range_coeMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution (hP : IsCayley k r ε P) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ UH (Hpk k r)) : ∃ g : UJ ε, Matrix.of (iota P g) = x := by
  have h : P * x * P⁻¹ ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact forth_mem hP hx
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  show P⁻¹ * coeMatrixAlt ε g * P = x
  rw [hg, back_forth hP]
end CompanionTheory.LimBd.SchurHpk
