-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.norm_sum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:20.981809+00:00
-- url     : https://prove2.me/submissions/2a7961ce-7179-4189-8550-8afd7c7f9ccf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.TraceQuadraticBound
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.Geo.Rec.TraceQuadraticBound
theorem _root_.solution (a w : n → ℂ) : ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖w k‖ ^ 2 := by
  have h1 : ‖∑ k, a k * w k‖ ≤ ∑ k, ‖a k‖ * ‖w k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖w k‖)
  have h0 : 0 ≤ ‖∑ k, a k * w k‖ := norm_nonneg _
  calc ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖w k‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2
end Formalism.L2.Geo.Rec.TraceQuadraticBound
