-- Prove2me | solution 1 for Formalism.L2.Col.HX_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:52.060159+00:00
-- url     : https://prove2.me/submissions/aafdfd89-9b72-4592-817e-b3fb81c71dcf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (n k t j : ℕ) : HX κ n k t j = HJ κ n (k + j) t j := rfl
end Formalism.L2.Col
