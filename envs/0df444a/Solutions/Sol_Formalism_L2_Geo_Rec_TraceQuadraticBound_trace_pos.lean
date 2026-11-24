-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.trace_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:16.353411+00:00
-- url     : https://prove2.me/submissions/50e09534-d81a-44c4-832c-c8fcc0816f2c

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
theorem _root_.solution {b : Matrix n n ℂ} (hb : b.PosSemidef) (hb0 : b ≠ 0) (Y : Matrix n n ℂ)
    (hY : IsUnit Y.det) : 0 < (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have e3 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, hH, e3]
  by_contra hle
  have hs : ∑ j, ∑ k, ‖H k j‖ ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity)
  have hH0 : H = 0 := by
    ext k j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => by positivity)).1 hs j
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h1 k (Finset.mem_univ _)
    simpa using h2
  apply hb0
  have hYi : IsUnit Yᴴ.det := by rw [det_conjTranspose]; exact hY.star
  have hz : Yᴴ * b * Y = 0 := by rw [hH, hH0]; simp
  calc b = (Yᴴ⁻¹ * Yᴴ) * b * (Y * Y⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hYi, Matrix.mul_nonsing_inv _ hY]; simp
    _ = Yᴴ⁻¹ * (Yᴴ * b * Y) * Y⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp
end Formalism.L2.Geo.Rec.TraceQuadraticBound
