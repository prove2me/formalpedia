-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_outright
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:48.066294+00:00
-- url     : https://prove2.me/submissions/e0ecce7d-0ce2-4531-80b1-6238fbc240d0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZAll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountFinal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountOut
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_zero_density_box
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_boxCountHyp_of_zeroDensityBox


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
theorem _root_.solution : ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C :=
  boxCountHyp_of_zeroDensityBox ZD.zero_density_box
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
