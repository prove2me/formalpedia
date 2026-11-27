-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.ge_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:36:31.341558+00:00
-- url     : https://prove2.me/submissions/2c7592eb-ef4b-428c-bc59-68e2d995527a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_geom_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w : ℝ} (h : V.Ge w (A - B)) (n : ℕ) :
    V.Ge w (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact (geom_int hA hB n).mul_int h
end Formalism.L2.FormalSeriesBounds.GmExArith
