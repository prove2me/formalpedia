-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.gam_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:17.924925+00:00
-- url     : https://prove2.me/submissions/5c9c8928-72c8-4f89-b3f4-c7a3847dc9ec

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution {l : ℕ} (hl : 1 < l) : gam l ≤ 1 / ((l : ℝ) - 1) := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  unfold gam
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
