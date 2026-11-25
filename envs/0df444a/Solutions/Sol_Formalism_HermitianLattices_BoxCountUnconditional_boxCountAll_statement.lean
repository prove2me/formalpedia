-- Prove2me | solution 1 for Formalism.HermitianLattices.BoxCountUnconditional.boxCountAll_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:57.400806+00:00
-- url     : https://prove2.me/submissions/ee6f67b9-4055-4ea0-a040-81a1867cc08e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_BoxCountAll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountOut
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BoxCountAllStatement
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_boxCountHyp_outright


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.BoxCountUnconditional
namespace Formalism.HermitianLattices.BoxCountUnconditional
theorem _root_.solution : BoxCountAll := Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_outright
end Formalism.HermitianLattices.BoxCountUnconditional
