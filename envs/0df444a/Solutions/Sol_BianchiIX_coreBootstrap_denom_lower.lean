-- Prove2me | solution 1 for BianchiIX.coreBootstrap_denom_lower
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:00:31.033785+00:00
-- url     : https://prove2.me/submissions/1c6a5cda-0755-4d19-93b9-98a2e877de31

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

end
end

/-- Completing the active-wall square keeps the projective chart regular even at zero walls. -/
theorem solution {k m u v w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    2 ≤ projectiveDenom m u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have huw := mul_le_mul hu' hw' hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)
  unfold projectiveDenom curvature
  nlinarith [sq_nonneg m, sq_nonneg (v - u - w)]
