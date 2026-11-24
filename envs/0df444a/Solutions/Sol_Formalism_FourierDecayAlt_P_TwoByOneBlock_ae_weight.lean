-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.ae_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:48.302828+00:00
-- url     : https://prove2.me/submissions/3f79b329-c613-489b-aa9d-6173f6462b5f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_zW_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_zW_meas


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
theorem _root_.solution (k : ℕ) (T T' : ℝ) :
    ∀ᵐ ζ ∂((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k T T' ζ)), T * T' < Complex.normSq ζ := by
  rw [ae_withDensity_iff (zW_meas k T T')]
  have hnull : (volume : Measure ℂ) {ζ | Complex.normSq ζ = T * T'} = 0 := by
    refine measure_mono_null ?_ (Measure.addHaar_sphere (volume : Measure ℂ) 0 (√(T * T')))
    intro ζ hζ
    have hζ' : Complex.normSq ζ = T * T' := hζ
    rw [mem_sphere_zero_iff_norm, ← hζ', Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have : ∀ᵐ ζ ∂(volume : Measure ℂ), Complex.normSq ζ ≠ T * T' := by
    rw [ae_iff]; simpa using hnull
  filter_upwards [this] with ζ hζ h0
  by_contra hlt
  apply h0
  unfold zWeight
  rw [if_neg (fun hle => hlt (lt_of_le_of_ne hle (Ne.symm hζ)))]
  simp
end Formalism.FourierDecayAlt.P.TwoByOneBlock
