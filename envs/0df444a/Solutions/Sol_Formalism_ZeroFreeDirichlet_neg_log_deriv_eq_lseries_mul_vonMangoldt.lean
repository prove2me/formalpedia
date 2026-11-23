-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.neg_log_deriv_eq_lseries_mul_vonMangoldt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:21.308969+00:00
-- url     : https://prove2.me/submissions/3542071c-7a8d-4ea1-9c2f-6b9e386f0283

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {w : ℂ} (hw : 1 < w.re) : negLD χ w = LSeries (↗χ * ↗Λ) w := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hw, neg_div]
  have hEq : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s = L (fun n => χ n) s :=
    fun s hs => DirichletCharacter.LFunction_eq_LSeries χ hs
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 w] L (fun n => χ n) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with s hs
    exact hEq s hs
  rw [hev.deriv_eq, hEq w hw]
end Formalism.ZeroFreeDirichlet
