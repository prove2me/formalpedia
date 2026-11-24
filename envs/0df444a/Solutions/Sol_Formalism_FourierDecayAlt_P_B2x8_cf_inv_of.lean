-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cf_inv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:40.907307+00:00
-- url     : https://prove2.me/submissions/9b60cf17-8835-4b77-adbf-f9da2803be3a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cone_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_mulVec_meas

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (g : Mat k (1 + r')) (T : ℂ × HPar k r' → ℂ × HPar k r')
    (hT : MeasurePreserving T (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))))
    (h : ∀ᵐ p ∂(μx.prod (volume : Measure (HPar k r'))), g *ᵥ Ψt k r' p = Ψt k r' (T p)) :
    (coneMeas k r').map (fun x => g *ᵥ x) = coneMeas k r' := by
  rw [cone_eq, Measure.map_map (cf_mulVec_meas g) Ψt_meas]
  rw [Measure.map_congr (show (fun x => g *ᵥ x) ∘ Ψt k r' =ᵐ[μx.prod (volume : Measure (HPar k r'))] Ψt k r' ∘ T from h)]
  rw [← Measure.map_map Ψt_meas hT.measurable, hT.map_eq]
end Formalism.FourierDecayAlt.P.B2x8
