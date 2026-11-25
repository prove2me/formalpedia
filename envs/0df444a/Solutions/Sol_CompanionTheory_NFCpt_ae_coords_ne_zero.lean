-- Prove2me | solution 1 for CompanionTheory.NFCpt.ae_coords_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:36.74654+00:00
-- url     : https://prove2.me/submissions/3edcebbb-ab28-4f3a-b778-b2dc5cc0da3a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology
namespace CompanionTheory.NFCpt
theorem _root_.solution (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ a, c a ≠ 0 := by
  rw [ae_all_iff]
  intro a
  have h : (volume : Measure (Fin n → ℂ)) {c | c a = 0} = 0 := Measure.pi_hyperplane _ a 0
  rw [ae_iff]
  simpa using h
end CompanionTheory.NFCpt
