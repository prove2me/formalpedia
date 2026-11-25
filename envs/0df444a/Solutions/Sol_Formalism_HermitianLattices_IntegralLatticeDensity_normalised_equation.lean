-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.normalised_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:40.587831+00:00
-- url     : https://prove2.me/submissions/153f10c4-ecf2-4651-b08b-a18c04d9f103

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Theorems.Thm_Formalism_HermitianLattices_IntegralLatticeDensity_normalised_equation_general

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
theorem _root_.solution : EqNormalised := by
  unfold EqNormalised
  intro E _ _ Ψ A _ ι χ G G' Γ Γ' _ _ _ _ j j' dt dt' dr dr' V _ _ pull Th M M' h1 h2 h3 h4
    γ γ' g g'
  have := normalised_equation_general E Ψ A ι χ G G' Γ Γ' j j' dt dt' dr dr' V pull Th M M'
    h1 h2 h3 h4 (M' : ℤ) (-(M : ℤ)) γ γ' g g'
  rw [this]
  simp
end Formalism.HermitianLattices.IntegralLatticeDensity
