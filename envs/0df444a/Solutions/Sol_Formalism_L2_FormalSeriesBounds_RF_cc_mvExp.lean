-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.cc_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:38.775158+00:00
-- url     : https://prove2.me/submissions/779e8ec1-0032-417a-a5cf-eca742aa4910

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (x : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp x) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (x ^ k) / (k.factorial : C)) = 1
  simp
end Formalism.L2.FormalSeriesBounds.RF
