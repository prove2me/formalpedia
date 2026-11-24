-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.liftM_add_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:21.644577+00:00
-- url     : https://prove2.me/submissions/74b37d64-f795-49ac-a874-16ae5e760944

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
    (a b : E) : liftM M (σ (a + b)) = liftM M (σ a) + liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a + b)), IntermediateField.coe_add, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_add]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
