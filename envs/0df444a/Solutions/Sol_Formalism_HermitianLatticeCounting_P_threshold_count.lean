-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.threshold_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:39.431406+00:00
-- url     : https://prove2.me/submissions/b55f8fbf-c2e7-440e-9af6-01e3e0194306

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ThreshCount := by
  intro n q h hh
  have e : Real.sqrt (2*(q:ℝ)) = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) _
  rw [e]
  have h2 : Real.sqrt 2 ≤ 23/16 := by rw [Real.sqrt_le_iff]; norm_num
  have hq := Real.sqrt_nonneg (q:ℝ)
  have hn : (0:ℝ) ≤ (n:ℝ)^2 := by positivity
  have := mul_le_mul_of_nonneg_right h2 (mul_nonneg hn hq)
  nlinarith
end Formalism.HermitianLatticeCounting.P
