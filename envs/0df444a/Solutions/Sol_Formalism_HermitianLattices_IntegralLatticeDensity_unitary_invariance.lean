-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.unitary_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:49.639685+00:00
-- url     : https://prove2.me/submissions/53165b00-b92f-4a4d-a672-53b2e7ac7b24

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset PD
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : UnitaryInvariance := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n _ _ δ hδ u
  have hG : ∀ a j, a ≠ j → ∑ i, star (δ i a) * δ i j = 0 := by
    intro a j hne
    have := congrFun (congrFun hδ a) j
    simpa [Matrix.mul_apply, Matrix.one_apply_ne hne] using this
  have hN : ∀ j, ∑ i, nm (δ i j) = 1 := by
    intro j
    apply hinj
    have := congrFun (congrFun hδ j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    rw [map_sum, map_one]
    simpa [hnm] using this
  rw [diag' h1 h2 h3 δ hG u Finset.univ]
  simp [hN]
end Formalism.HermitianLattices.IntegralLatticeDensity
