-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.eps_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:29.896514+00:00
-- url     : https://prove2.me/submissions/4e8c61b8-73ba-4343-9863-3c94221f8f93

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_rr_gt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) : eps a ≤ 1 / 16 := by
  have h := (rr_gt a).le
  unfold eps
  exact one_div_le_one_div_of_le (by norm_num) h
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
