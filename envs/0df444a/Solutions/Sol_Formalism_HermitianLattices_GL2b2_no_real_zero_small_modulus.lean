-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.no_real_zero_small_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:53.445798+00:00
-- url     : https://prove2.me/submissions/ea87c94e-6e7d-405f-8208-0f9f24eb3add

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_noRealZeroSmall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
namespace Formalism.HermitianLattices.GL2b2
theorem _root_.solution : NoRealZeroSmall := PfN.noRealZeroSmall
end Formalism.HermitianLattices.GL2b2
