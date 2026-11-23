-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.twentyFive_mul_smallConstant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:29.836261+00:00
-- url     : https://prove2.me/submissions/c38ba18e-aa29-44a8-9d9d-7501f889b5f2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant

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
theorem _root_.solution (a : ℕ) : 25 * c0 a = 1 / rr a := by
  unfold c0
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
