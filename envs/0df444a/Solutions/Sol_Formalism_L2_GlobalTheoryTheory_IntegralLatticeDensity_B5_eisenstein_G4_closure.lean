-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.eisenstein_G4_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:17.027171+00:00
-- url     : https://prove2.me/submissions/b75ea15c-60ac-40ea-af2d-5b4445852564

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_jac_eisG
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_E4_eq_half_eisensteinSeries

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
    eisG (AddSubgroup.closure {a, a * z}) 2 =
      (a ^ 4)⁻¹ * (2 * ((Real.pi : ℂ) ^ 4 / 90) * ModularForm.E₄ (⟨z, hz⟩ : UpperHalfPlane)) := by
  rw [jac_eisG a z ha hz 2 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 4) (by norm_num) (⟨z, hz⟩ : UpperHalfPlane)
  rw [show ((2 * 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, h2, E4_eq_half_eisensteinSeries,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four, show a ^ (2 * 2) = a ^ 4 by norm_num]
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
