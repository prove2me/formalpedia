-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.Kf_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:29.050949+00:00
-- url     : https://prove2.me/submissions/661f15b5-99af-46e9-80c3-8a279021421e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {n m : ℕ} (h : n ≤ m) : Kf ε n ≤ Kf ε m := by
  unfold Kf
  exact Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast h) hε.le)
end Formalism.L2.FormalSeriesBounds.GmExArith
