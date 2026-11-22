-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_re_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:21.064808+00:00
-- url     : https://prove2.me/submissions/dbbcb9dc-9d88-4cea-a217-5995a0239047

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
theorem _root_.solution (x : ℝ) :
    Schi χ x = (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) := by
  unfold Schi Formalism.Sa vonMangoldtCharRe vonMangoldtCharIm
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [← Complex.re_add_im (χ (n : ZMod q))]
  ring
end Formalism.ZeroFreeDirichlet
