-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.negLD_eq_LSeries_mul_vonMangoldt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:10.334266+00:00
-- url     : https://prove2.me/submissions/977b5861-6f08-4a72-84da-7aafe29c8561

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries ↗χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [negLD, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div]
end Formalism.ZeroFreeDirichlet
