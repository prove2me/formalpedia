-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.cube_elimination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:16.68818+00:00
-- url     : https://prove2.me/submissions/1f9bd793-688a-468b-8c8b-a34ed06a9eb0

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
theorem _root_.solution : CubeEliminate := by
  unfold CubeEliminate
  intro M Q _ _ φ hpar hcube
  have hi : ∀ a b c, φ (a + b + c) - φ (a + b) - φ (b + c) - φ (c + a) + φ a + φ b + φ c = 0 := by
    intro a b c
    calc φ (a + b + c) - φ (a + b) - φ (b + c) - φ (c + a) + φ a + φ b + φ c
        = (φ (a + b + c) + φ (a - b) + φ (b - c) + φ (c - a)) - (φ (a + b) + φ (a - b))
            - (φ (b + c) + φ (b - c)) - (φ (c + a) + φ (c - a)) + φ a + φ b + φ c := by abel
      _ = 3 • (φ a + φ b + φ c) - (2 • φ a + 2 • φ b) - (2 • φ b + 2 • φ c)
            - (2 • φ c + 2 • φ a) + φ a + φ b + φ c := by
          rw [hcube, hpar a b, hpar b c, hpar c a]
      _ = 0 := by abel
  refine ⟨hi, fun a a' b => ?_⟩
  simp only [cob]
  have := hi a a' b
  rw [add_comm b a] at this
  rw [← sub_eq_zero, ← this]
  abel
end Formalism.HermitianLattices.IntegralLatticeDensity
