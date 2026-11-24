-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.eisenstein_G6_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:17.808223+00:00
-- url     : https://prove2.me/submissions/45152044-a942-4d86-b4aa-d3d9ce6743a2

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_jac_riemannZeta_six
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_jac_eisG
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_E6_eq_half_eisensteinSeries

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
    eisG (AddSubgroup.closure {a, a * z}) 3 =
      (a ^ 6)⁻¹ * (2 * ((Real.pi : ℂ) ^ 6 / 945) * ModularForm.E₆ (⟨z, hz⟩ : UpperHalfPlane)) := by
  rw [jac_eisG a z ha hz 3 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by norm_num) (⟨z, hz⟩ : UpperHalfPlane)
  rw [show ((2 * 3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num, h2, E6_eq_half_eisensteinSeries,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, jac_riemannZeta_six, show a ^ (2 * 3) = a ^ 6 by norm_num]
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
