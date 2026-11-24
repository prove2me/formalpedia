-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:16:05.177721+00:00
-- url     : https://prove2.me/submissions/5931b2e7-f589-48e3-b9d9-bcb608375dfd

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharRe_zero
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharIm_zero
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_re_im
import Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_function_continuousAt

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
theorem _root_.solution (y : ℝ) : ContinuousAt (fun x => Schi χ x) y := by
  have h : (fun x => Schi χ x) =
      fun x => (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) :=
    funext (chebyshev_character_re_im χ)
  rw [h]
  exact (summatory_function_continuousAt (vonMangoldtCharRe_zero χ) y).add
    (continuousAt_const.mul (summatory_function_continuousAt (vonMangoldtCharIm_zero χ) y))
end Formalism.ZeroFreeDirichlet
