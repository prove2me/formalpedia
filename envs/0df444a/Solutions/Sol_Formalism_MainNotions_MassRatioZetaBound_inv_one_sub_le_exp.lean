-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.inv_one_sub_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:00.998507+00:00
-- url     : https://prove2.me/submissions/994f2e4a-a9b2-4704-862b-6b494e542fdf

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  calc (1 - x)⁻¹ ≤ 1 + 2 * x := by
        rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
    _ ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
end Formalism.MainNotions.MassRatioZetaBound
