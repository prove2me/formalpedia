-- Prove2me | solution 1 for Formalism.L2.Col.add_sum_replicate_eq_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:09:48.615073+00:00
-- url     : https://prove2.me/submissions/a5dbb835-bfd0-4eb2-a7eb-0edd64a64962

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
namespace Formalism.L2.Col
theorem _root_.solution (r t j : ℕ) : r + (List.replicate j t).sum = r + j * t := by
  rw [List.sum_replicate, smul_eq_mul]
end Formalism.L2.Col
