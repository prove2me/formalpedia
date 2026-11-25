-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroDensityInBoxes.box_tail_bound_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:38:29.368191+00:00
-- url     : https://prove2.me/submissions/96f22e84-b99e-4708-a701-247634d7cb8a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ZeroDensityBox
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailFinal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountFinal
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BoxCountOfZeroDensity
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_box_tail_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroDensityInBoxes
namespace Formalism.HermitianLattices.ZeroDensityInBoxes
theorem _root_.solution : BoxTailAll := Formalism.HermitianLattices.Ext.BoxTail.box_tail_bound
end Formalism.HermitianLattices.ZeroDensityInBoxes
