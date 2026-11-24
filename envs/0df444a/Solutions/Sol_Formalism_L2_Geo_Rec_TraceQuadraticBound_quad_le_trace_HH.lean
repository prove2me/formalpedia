-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.quad_le_trace_HH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:14.025604+00:00
-- url     : https://prove2.me/submissions/5d987514-09a0-4aec-9cb7-e1d9a946e3ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_re_star_dot_self
import Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_norm_sum_sq_le

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
theorem _root_.solution (H : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ (Hᴴ * H) *ᵥ w).re ≤ (Hᴴ * H).trace.re * ∑ i, ‖w i‖ ^ 2 := by
  have e1 : star w ⬝ᵥ (Hᴴ * H) *ᵥ w = star (H *ᵥ w) ⬝ᵥ (H *ᵥ w) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  rw [e1, re_star_dot_self]
  have e2 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  exact norm_sum_sq_le (fun j => H k j) w
end Formalism.L2.Geo.Rec.TraceQuadraticBound
