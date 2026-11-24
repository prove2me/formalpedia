-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.l_log_deriv_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:54.221799+00:00
-- url     : https://prove2.me/submissions/8edbe4b0-245d-4ca7-9dcc-2ef886c7cad8

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Theorems.Thm_Formalism_ZeroFreeDirichlet_negLD_eq_LSeries_mul_vonMangoldt
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_LSeries_twist_vonMangoldt_le
import Theorems.Thm_Formalism_ZF_lamF_eq_norm
import Theorems.Thm_Formalism_ZF_logDerivBoundRightHalfPlane


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
theorem _root_.solution : LLogDerivRight := by
  obtain ⟨C, hC0, hC⟩ := Formalism.ZF.logDerivBoundRightHalfPlane
  refine ⟨C, hC0, ?_⟩
  intro q _ χ s hs
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs]
  refine le_trans (norm_LSeries_twist_vonMangoldt_le χ hs) ?_
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  rw [Formalism.ZF.lamF_eq_norm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, norm_neg]
  have h := hC (s.re : ℂ) hre
  simpa using h
end Formalism.ZeroFreeDirichlet
