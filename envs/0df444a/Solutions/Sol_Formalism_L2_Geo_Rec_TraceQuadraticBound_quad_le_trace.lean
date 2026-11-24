-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.quad_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:00.371536+00:00
-- url     : https://prove2.me/submissions/2a9cc760-9ec3-454f-98b6-d43d4aa52bc1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_exists_star_mul_self
import Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_quad_le_trace_HH

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
theorem _root_.solution {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) (w : n → ℂ) :
    (star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w)).re ≤ (b * (Y * Yᴴ)).trace.re * ∑ i, ‖w i‖ ^ 2 := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e1 : star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w) = star w ⬝ᵥ (Yᴴ * b * Y) *ᵥ w := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e1, e2, hH]
  exact quad_le_trace_HH H w
end Formalism.L2.Geo.Rec.TraceQuadraticBound
