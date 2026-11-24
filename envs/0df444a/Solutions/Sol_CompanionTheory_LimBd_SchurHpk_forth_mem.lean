-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.forth_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:31:29.926819+00:00
-- url     : https://prove2.me/submissions/ee4611db-8810-4ce4-b806-a5bf25ab3d64

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
theorem _root_.solution (hP : IsCayley k r ε P) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ UH (Hpk k r)) : P * x * P⁻¹ ∈ UJset ε := by
  have hx' : xᴴ * (Pᴴ * Jm ε * P) * x = Pᴴ * Jm ε * P := by rw [hP.2]; exact hx
  have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, P_mul_inv hP, Matrix.conjTranspose_one]
  show (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε
  calc (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = P⁻¹ᴴ * (xᴴ * (Pᴴ * Jm ε * P) * x) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hx']; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, P_mul_inv hP, Matrix.one_mul, Matrix.mul_one]
end CompanionTheory.LimBd.SchurHpk
