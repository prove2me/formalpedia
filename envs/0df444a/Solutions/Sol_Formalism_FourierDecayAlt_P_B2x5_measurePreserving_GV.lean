-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.measurePreserving_GV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:57.907904+00:00
-- url     : https://prove2.me/submissions/6fd61bb3-f6f9-474b-a57f-f7e39bac0ee4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_normSq_det_GV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) :
    MeasurePreserving (fun y : Fin (2 * r + k + 1) → ℂ => g *ᵥ y) volume volume := by
  have hn := normSq_det_GV hg
  set f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.toLin' g).restrictScalars ℝ with hf
  have hfg : (fun y : Fin (2 * r + k + 1) → ℂ => g *ᵥ y) = f := by
    funext y
    simp [hf, Matrix.toLin'_apply]
  have hd : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hn]
  rw [hfg]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hd]; norm_num), hd]
  simp
end Formalism.FourierDecayAlt.P.B2x5
