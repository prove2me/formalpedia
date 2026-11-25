-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.main_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:54.988694+00:00
-- url     : https://prove2.me/submissions/d5aa4d69-ea08-4648-b4dd-88408999f823

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (J : ℕ) (c b : C) (h : D.lev b ≠ D.lev c + 1) : D.main J c b = 0 := by
  unfold main
  split_ifs with h1
  · rw [D.g_supp c h1.2 b h, mul_zero, map_zero, zero_mul]
  · rfl
end Formalism.BaseCaseIdentities.Data
