-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.dot_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:36.506527+00:00
-- url     : https://prove2.me/submissions/6ef97ccf-9a8b-49bd-991c-e77337bdde3f

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_inv_eq_ct
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
theorem _root_.solution (hP : IsCayleyU k r ε P) (a : B.Mat k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    star (P *ᵥ y) ⬝ᵥ ((P * a * P⁻¹) *ᵥ (P *ᵥ x)) = star y ⬝ᵥ (a *ᵥ x) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← inv_eq_ct hP]
  congr 2
  calc P⁻¹ * (P * a * P⁻¹ * P) = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = a := by rw [inv_mul_P hP.1, Matrix.one_mul, Matrix.mul_one]
end CompanionTheory.LimBd.Main
