-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.jetAt0_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:27.069613+00:00
-- url     : https://prove2.me/submissions/093fc8a4-9bef-4795-aba4-c5cb7b9a1841

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
theorem _root_.solution (G : MvPowerSeries σ C) : jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  unfold jetAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simp [mfact]
end Formalism.L2.FormalSeriesBounds.RF
