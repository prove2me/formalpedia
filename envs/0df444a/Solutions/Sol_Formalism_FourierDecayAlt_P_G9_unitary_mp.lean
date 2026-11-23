-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.unitary_mp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:28.652075+00:00
-- url     : https://prove2.me/submissions/253b27f9-b018-4b2e-91a2-34f4135dae11

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_norm_det_unitary

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
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    MeasurePreserving (fun x : Fin d → ℂ => W *ᵥ x) (muPi β (Fin d)) (muPi β (Fin d)) := by
  have hc : Real.toNNReal (‖β‖ / (2 * Real.pi)) ≠ 0 := by
    have : 0 < ‖β‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
    exact (Real.toNNReal_pos.2 this).ne'
  have : (mu β).IsAddHaarMeasure := by
    unfold mu; exact Measure.IsAddHaarMeasure.nnreal_smul _ hc
  have : (muPi β (Fin d)).IsAddHaarMeasure := by
    unfold muPi; infer_instance
  have hdet : LinearMap.det ((Matrix.toLin' W).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, norm_det_unitary hW, one_pow]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (muPi β (Fin d))
    (f := (Matrix.toLin' W).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  refine ⟨?_, h⟩
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable
end Formalism.FourierDecayAlt.P.G9
