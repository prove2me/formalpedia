-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_deriv_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:02.836347+00:00
-- url     : https://prove2.me/submissions/4ce72864-2dbe-41b9-81cf-a967932601ce

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution (m : ℕ) (c : ℕ → ℂ) :
    HasDerivAt (fun t : ℂ => ∑ j ∈ Finset.range (m + 1 + 1), c j * t ^ (m + 1 - j)) (c m) 0 := by
  have h : ∀ j ∈ Finset.range (m + 1 + 1), HasDerivAt (fun t : ℂ => c j * t ^ (m + 1 - j))
      (c j * (((m + 1 - j : ℕ) : ℂ) * (0 : ℂ) ^ (m + 1 - j - 1))) 0 := fun j _ =>
    (hasDerivAt_pow (m + 1 - j) (0 : ℂ)).const_mul (c j)
  have h2 := HasDerivAt.fun_sum h
  refine h2.congr_deriv ?_
  rw [Finset.sum_eq_single m]
  · simp
  · intro j hj hne
    have : j < m + 1 + 1 := Finset.mem_range.mp hj
    by_cases hj' : j = m + 1
    · subst hj'; simp
    · rw [zero_pow (by omega)]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
end Formalism.FourierDecayAlt.P.StandardCharacterExists
