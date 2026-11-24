-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.frame_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:20.011327+00:00
-- url     : https://prove2.me/submissions/a989f693-adfe-433e-a94c-75e00f1edd19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_exists_star_mul_self

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
theorem _root_.solution {A : Matrix n n ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) :
    ∃ X : Matrix n n ℂ, X * Xᴴ = A ∧ IsUnit X.det := by
  obtain ⟨B, rfl⟩ := exists_star_mul_self hA
  refine ⟨Bᴴ, by rw [conjTranspose_conjTranspose], ?_⟩
  rw [det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd)
end Formalism.L2.Geo.Rec.TraceQuadraticBound
