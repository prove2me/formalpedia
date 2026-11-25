-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.prime_sums_short_interval_lower_bound_of_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:03:46.614141+00:00
-- url     : https://prove2.me/submissions/73b645d2-a03f-437a-b060-acba4f1cd042

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : ShortIntervalLowerBound → Formalism.HermitianLattices.GL2PrimeSums.ShortIntervalLowerBound := by
  intro hL C₀ Cr cr cb h1 h2 h3 h4
  obtain ⟨C₀', c, hC, hc, H⟩ := hL C₀ Cr cr cb h1 h2 h3 h4
  refine ⟨C₀', c, hC, hc, ?_⟩
  intro B G β θ π₁ π₂ hB hG1 hGB hθ hβ hπ₂ hQ X hX
  exact H B G β θ π₁ π₂ (fun _ => 0) hB hG1 hGB hθ hβ hπ₂
    (fun _ => ⟨le_refl _, by
      show (0 : ℝ) ≤ 3 * Real.log B
      have := Real.log_nonneg (show (1 : ℝ) ≤ B by linarith)
      linarith⟩)
    (fun Y hY => by
      show |G * ((π₁ Y : ℝ) + π₂ Y + 0) - _| ≤ _
      rw [add_zero]
      exact hQ Y hY) X hX
end Formalism.HermitianLattices.GlobalBoundRefinements
