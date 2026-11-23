-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.eps_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:12.87591+00:00
-- url     : https://prove2.me/submissions/fb9b2915-ba10-4631-9bf2-34e1f26e2b23

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
private theorem rr_pos' (a : ℕ) : 0 < rr a := by
  unfold rr
  positivity
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) : 0 < eps a := by
  unfold eps
  exact div_pos one_pos (rr_pos' a)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
