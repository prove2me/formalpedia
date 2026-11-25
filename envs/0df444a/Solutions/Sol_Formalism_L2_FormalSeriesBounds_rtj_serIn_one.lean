-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_serIn_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:43.570782+00:00
-- url     : https://prove2.me/submissions/a8004787-8fb4-4937-8da9-24fbfc792458

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

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
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (A : Set σ) : rtjSerIn A (1 : MvPowerSeries σ K) := by
  unfold rtjSerIn
  intro μ hμ
  rw [MvPowerSeries.coeff_one] at hμ
  split_ifs at hμ with h0
  · subst h0
    simp
  · exact absurd rfl hμ
end Formalism.L2.FormalSeriesBounds
