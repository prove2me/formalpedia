-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:37.428388+00:00
-- url     : https://prove2.me/submissions/6a4786f0-cc93-47a3-8763-cfb49d803c93

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentArithmeticBound
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_PropZ_i_of
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_second_zeta_mean_bound
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_third_zeta_application


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
theorem _root_.solution : PropZ_i := PropZ_i_of second_zeta_mean_bound third_zeta_application
end Formalism.HermitianLattices.TraceIntegrality
