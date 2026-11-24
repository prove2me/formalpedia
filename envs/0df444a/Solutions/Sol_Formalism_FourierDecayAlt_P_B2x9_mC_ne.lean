-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.mC_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:52.338939+00:00
-- url     : https://prove2.me/submissions/974877f3-f2ba-4acb-9952-cfce4890a4a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_wt_meas

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution : mC k r' ≠ 0 := by
  intro h
  have h1 : wt k r' =ᵐ[volume] 0 := by
    unfold mC at h
    first
      | exact withDensity_eq_zero wt_meas.aemeasurable h
      | exact (withDensity_eq_zero_iff wt_meas.aemeasurable).1 h
  have h2 : ∀ᵐ c : ℂ ∂volume, c = 0 := by
    filter_upwards [h1] with c hc
    simp only [wt, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hc
    by_contra hne
    have : 0 < ‖c‖ ^ (2 * (2 * r' + k + 1)) := pow_pos (norm_pos_iff.2 hne) _
    linarith
  have h3 : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℂ) : (volume : Measure ℂ) {0} = 0)
  have h4 : ∀ᵐ _c : ℂ ∂volume, False := by
    filter_upwards [h2, h3] with c a b using b a
  rw [ae_iff] at h4
  first
    | simp at h4
    | exact (NeZero.ne (volume : Measure ℂ)) (Measure.measure_univ_eq_zero.1 (by simpa using h4))
end Formalism.FourierDecayAlt.P.B2x9
