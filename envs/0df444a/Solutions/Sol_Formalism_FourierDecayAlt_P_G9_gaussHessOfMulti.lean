-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.gaussHessOfMulti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:09.630611+00:00
-- url     : https://prove2.me/submissions/6f9e220a-a7f0-405f-a071-c5bb151056e8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution : GaussHessOfMulti := by
  intro hG hD m β t z hβ ht hz
  have hdet : (z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det ≠ 0 := by
    rw [hD m z]
    have : ((m:ℂ)+2) ≠ 0 := by
      have : ((m:ℂ)+2) = ((m+2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (Nat.succ_ne_zero (m+1))
    exact mul_ne_zero this (pow_ne_zero _ (inv_ne_zero hz))
  have hs : (z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).IsSymm := by
    ext i j; simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm, mul_add]
  have h := hG (m+1) β t _ hβ ht hs hdet
  rw [hD m z] at h
  convert h using 3
  have h2 : ‖(m:ℂ)+2‖ = (m:ℝ)+2 := by
    have : ((m:ℂ)+2) = (((m:ℝ)+2 : ℝ):ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, norm_pow, norm_inv, h2]
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  field_simp
  rw [← mul_pow]; simp [this.ne']
end Formalism.FourierDecayAlt.P.G9
