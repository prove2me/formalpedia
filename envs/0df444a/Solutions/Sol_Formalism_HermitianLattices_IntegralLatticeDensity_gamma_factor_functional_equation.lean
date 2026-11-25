-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.gamma_factor_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:21.443302+00:00
-- url     : https://prove2.me/submissions/0e2d6e4d-9abb-4291-b450-6a0ae8780a56

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_logarithm_series_coefficient_identities


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
theorem _root_.solution : GcFunEq := by
  intro K _ _ σ c p hp hc a b
  obtain ⟨_, h⟩ := logarithm_series_coefficient_identities p hp
  have h1 := congrArg (Rat.cast : ℚ → K) (h a b)
  have h2 := congrArg (Rat.cast : ℚ → K) (h b a)
  have hB : ∀ x y, coefB p x y = coefA p y x := fun _ _ => rfl
  by_cases hab : p ∣ a ∧ p ∣ b
  · have hba : p ∣ b ∧ p ∣ a := ⟨hab.2, hab.1⟩
    rw [if_pos hab] at h1 ⊢
    rw [if_pos hba] at h2
    push_cast at h1 h2
    rw [hB (a / p) (b / p), h1, h2, hc]
    simp only [hB]
    ring
  · have hba : ¬ (p ∣ b ∧ p ∣ a) := fun h => hab ⟨h.2, h.1⟩
    rw [if_neg hab] at h1 ⊢
    rw [if_neg hba] at h2
    push_cast at h1 h2
    rw [hB] at h1 h2 ⊢
    linear_combination (σ c) * h1 - c * h2
end Formalism.HermitianLattices.IntegralLatticeDensity
