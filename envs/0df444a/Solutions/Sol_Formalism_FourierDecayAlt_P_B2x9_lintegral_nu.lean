-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.lintegral_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:36.755117+00:00
-- url     : https://prove2.me/submissions/c1d5456d-e63e-4d65-9755-722fa1e02749

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Psi_meas
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
theorem _root_.solution (μG₁ : Measure (Mt k r')) [SFinite μG₁] (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(nu μG₁) = II μG₁ f := by
  unfold nu II
  rw [lintegral_map hf Psi_meas]
  first
    | rw [lintegral_prod (fun a => f (Psi k r' a)) ((hf.comp Psi_meas).aemeasurable)]
    | rw [lintegral_prod _ (hf.comp Psi_meas).aemeasurable]
  unfold mC
  rw [lintegral_withDensity_eq_lintegral_mul _ wt_meas]
  · rfl
  · exact (hf.comp Psi_meas).lintegral_prod_right'
end Formalism.FourierDecayAlt.P.B2x9
