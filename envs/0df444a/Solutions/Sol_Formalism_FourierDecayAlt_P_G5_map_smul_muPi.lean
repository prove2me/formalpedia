-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.map_smul_muPi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:19.624436+00:00
-- url     : https://prove2.me/submissions/7d30571a-7c6c-4978-9a44-f8140c840608

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_muPi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (β z : ℂ) (ι : Type) [Fintype ι] (hz : z ≠ 0) :
    Measure.map (fun v : ι → ℂ => z • v) (muPi β ι) =
      Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • muPi β ι := by
  classical
  have hdet : LinearMap.det ((z • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))).restrictScalars ℝ) =
      ‖z‖ ^ (2 * Fintype.card ι) := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm]
    simp
  have hpos : (0 : ℝ) < ‖z‖ ^ (2 * Fintype.card ι) := by positivity
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (z • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))).restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.2 hpos)] at h2
  have h3 : Measure.map (fun v : ι → ℂ => z • v) volume =
      ENNReal.ofReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • volume := h2
  rw [muPi_eq, Measure.map_smul, h3, smul_comm]
  rfl
end Formalism.FourierDecayAlt.P.G5
