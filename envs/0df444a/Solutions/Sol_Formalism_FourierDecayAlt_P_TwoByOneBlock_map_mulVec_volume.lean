-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.map_mulVec_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:30:57.995354+00:00
-- url     : https://prove2.me/submissions/47654e50-edad-4051-9a0b-69f6450966d8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h, one_pow]
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h2
  have h3 : Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume := h2
  simpa using h3
end Formalism.FourierDecayAlt.P.TwoByOneBlock
