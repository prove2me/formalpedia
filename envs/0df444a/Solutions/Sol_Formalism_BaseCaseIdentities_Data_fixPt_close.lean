-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.fixPt_close
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:14.592327+00:00
-- url     : https://prove2.me/submissions/1d54c0ff-f28b-40e6-b058-c831a80bbcae

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_iterate_zero

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
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (n : ℕ) (c : C) : OrdGE (n + 1) (D.fixPt c - (D.Psi)^[n] 0 c) := by
  intro A hA
  rw [map_sub, D.coeff_iterate_zero c A (by omega), sub_self]
end Formalism.BaseCaseIdentities.Data
