-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:48.203216+00:00
-- url     : https://prove2.me/submissions/333e0e68-6eef-4812-9056-8f4225339303

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_eisenstein_G4_closure
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_eisenstein_G6_closure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    discr (AddSubgroup.closure {a, a * z}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta z ^ 24 := by
  have hD := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq (⟨z, hz⟩ : UpperHalfPlane)
  have hD' : ModularForm.discriminant (⟨z, hz⟩ : UpperHalfPlane) = ModularForm.eta z ^ 24 := rfl
  rw [hD'] at hD
  rw [discr, g2, g3, eisenstein_G4_closure a z ha hz, eisenstein_G6_closure a z ha hz, hD]
  field_simp
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
