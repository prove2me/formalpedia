-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.liftM_mul_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:05.470023+00:00
-- url     : https://prove2.me/submissions/25f43d65-3a10-4982-a9f0-a10ee4755cea

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_val_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a * b)) = liftM M (σ a) * liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a * b)), IntermediateField.coe_mul, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_mul]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
