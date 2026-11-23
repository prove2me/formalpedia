-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.trace_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:39.051545+00:00
-- url     : https://prove2.me/submissions/21aec602-3ecc-48a5-b7d0-e43abef24ee0

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
theorem _root_.solution {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) :
    0 ≤ (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e2, hH]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity
end Formalism.L2.Geo.Rec.TraceQuadraticBound
