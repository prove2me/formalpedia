-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.second_zeta_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:00.660839+00:00
-- url     : https://prove2.me/submissions/20f7310e-c668-45a1-b2ad-9e08227d869e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_second_zeta_top_bound
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_second_zeta_thin_bound
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_second_zeta_mean_of_top_thin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : MeanLogNormBound := second_zeta_mean_of_top_thin second_zeta_top_bound second_zeta_thin_bound
end Formalism.HermitianLattices.TraceIntegrality
