-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.vonMangoldtCharIm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:10.371344+00:00
-- url     : https://prove2.me/submissions/6653ce76-9c6e-414b-97bc-97b7bba5e7ae

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
theorem _root_.solution : vonMangoldtCharIm χ 0 = 0 := by simp [vonMangoldtCharIm]
end Formalism.ZeroFreeDirichlet
