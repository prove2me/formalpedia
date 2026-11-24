-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.re_star_dot_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:11.518678+00:00
-- url     : https://prove2.me/submissions/6a3b7cc0-aa73-48df-bfbc-1bfa97f43556

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
theorem _root_.solution (v : n → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast
end Formalism.L2.Geo.Rec.TraceQuadraticBound
