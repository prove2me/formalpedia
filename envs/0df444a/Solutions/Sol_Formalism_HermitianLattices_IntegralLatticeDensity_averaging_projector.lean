-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.averaging_projector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:17.185795+00:00
-- url     : https://prove2.me/submissions/cf7ee007-50c8-4ae1-9b3b-557cc4229356

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : AverageProjector := by
  unfold AverageProjector
  intro K _ N ζ hN hζ w
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd w).2 h]
    simp
  · have hne : ζ ^ w ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd w).1 h')
    rw [geom_sum_eq hne]
    have h1 : (ζ ^ w) ^ N = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [h1, sub_self, zero_div]
end Formalism.HermitianLattices.IntegralLatticeDensity
