-- Prove2me | solution 1 for DiscrNeWork.discr_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:22.136927+00:00
-- url     : https://prove2.me/submissions/28ae3743-7fdc-41fe-8372-2bf07fbbd44c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
import Theorems.Thm_DiscrNeWork_eisenstein_four_lattice_eq
import Theorems.Thm_DiscrNeWork_eisenstein_six_lattice_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork
namespace DiscrNeWork
theorem _root_.solution (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : PI.discr (PI.lat2 a (a * τ)) ≠ 0 := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq] at hΔ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : PI.discr (PI.lat2 a (a * τ)) =
      (a ^ 12)⁻¹ * (64 / 27 * (Real.pi : ℂ) ^ 12) * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
    rw [PI.discr, PI.g2, PI.g3, eisenstein_four_lattice_eq a ha τ, eisenstein_six_lattice_eq a ha τ]
    ring
  rw [key]
  have h1 : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
    intro h; apply hΔ; rw [h]; simp
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ ha))
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hpi))) h1
end DiscrNeWork
