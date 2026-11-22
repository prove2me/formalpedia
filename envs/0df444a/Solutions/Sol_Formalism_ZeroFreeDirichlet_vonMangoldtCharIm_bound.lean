-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.vonMangoldtCharIm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:41.705645+00:00
-- url     : https://prove2.me/submissions/15b1b714-9965-456d-a581-ca69628678d5

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
theorem _root_.solution (n : ℕ) : |vonMangoldtCharIm χ n| ≤ 1 * Λ n := by
  unfold vonMangoldtCharIm
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_mul, abs_of_nonneg hΛ, one_mul]
  refine mul_le_of_le_one_right hΛ ?_
  refine le_trans ?_ (DirichletCharacter.norm_le_one χ (n : ZMod q))
  first
  | exact Complex.abs_im_le_norm _
  | exact Complex.abs_im_le_abs _
end Formalism.ZeroFreeDirichlet
