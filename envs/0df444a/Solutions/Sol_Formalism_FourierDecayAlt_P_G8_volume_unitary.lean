-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.volume_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:09.586116+00:00
-- url     : https://prove2.me/submissions/2acc9708-aff3-4c6a-a18f-80d0fb560745

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_normSq_det_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Measure.map (fun x : Fin d → ℂ => W *ᵥ x) (volume : Measure (Fin d → ℂ)) = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' W).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      normSq_det_unitary d W hW]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin d → ℂ))
    (f := (Matrix.toLin' W).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h
  have hf : (fun x : Fin d → ℂ => W *ᵥ x) = ⇑((Matrix.toLin' W).restrictScalars ℝ) := by
    ext x; simp
  rw [hf, h]; simp
end Formalism.FourierDecayAlt.P.G8
