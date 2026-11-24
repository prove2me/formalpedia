-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.forth_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:27.997238+00:00
-- url     : https://prove2.me/submissions/0e53e607-474e-458f-ba6c-12b4835c4056

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
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
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution (hP : IsCayley k r ε P) (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
  calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
        rw [inv_mul_P hP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]
end CompanionTheory.LimBd.SchurHpk
