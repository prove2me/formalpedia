-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.type_under_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:41.875262+00:00
-- url     : https://prove2.me/submissions/3c347d56-f482-471d-b415-8d6095013a26

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
theorem _root_.solution : TypeTwist := by
  intro K _ τ q hq ε η π hε hη hπ h lam
  simp only [map_mul, MvPowerSeries.map_C, MvPowerSeries.expand_C, map_inv₀, h]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 3
  field_simp
end Formalism.HermitianLattices.IntegralLatticeDensity
