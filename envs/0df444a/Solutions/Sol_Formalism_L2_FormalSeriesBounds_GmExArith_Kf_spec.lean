-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.Kf_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:15.385576+00:00
-- url     : https://prove2.me/submissions/87a15b6d-cd25-485a-9a67-19c1aea18551

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (n : ℕ) : (n : ℝ) ≤ (Kf ε n : ℝ) * ε := by
  have := Nat.le_ceil ((n : ℝ) / ε)
  unfold Kf
  rwa [div_le_iff₀ hε] at this
end Formalism.L2.FormalSeriesBounds.GmExArith
