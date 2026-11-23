-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.linear_prime_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:21.312837+00:00
-- url     : https://prove2.me/submissions/a34c5230-404a-4f6c-9fc0-82546e26e26b

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_linear_division_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_zero_of_X_sub_C_dvd_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : LinPrime := by
  intro O _ _ I _ c hc
  have hne : (X - C c : O⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    simp at this
  refine ⟨hne, ?_, ?_⟩
  · intro hu
    have : (X - C c : O⟦X⟧) ∣ C 1 := hu.dvd
    exact one_ne_zero (eq_zero_of_X_sub_C_dvd_C I c hc 1 this)
  · intro f g hfg
    obtain ⟨f₁, a, hf⟩ := (linear_division_holds O I c hc).1 f
    obtain ⟨g₁, b, hg⟩ := (linear_division_holds O I c hc).1 g
    have h1 : (X - C c : O⟦X⟧) ∣ C (a * b) := by
      have h2 : C (a * b) = f * g - (X - C c) * (f₁ * g + C a * g₁) := by
        rw [map_mul]
        conv_rhs => rw [hf]
        conv_rhs => rw [hg]
        ring
      rw [h2]
      exact dvd_sub hfg (dvd_mul_right _ _)
    rcases mul_eq_zero.mp (eq_zero_of_X_sub_C_dvd_C I c hc _ h1) with h | h
    · left; rw [hf, h]; simp
    · right; rw [hg, h]; simp
end Formalism.CohomologicalDescent.HeightDescentMinors
