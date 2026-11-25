-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.meas_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:36:49.068924+00:00
-- url     : https://prove2.me/submissions/025e25a8-5326-4eeb-abec-9d60dec4ea4a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_invM_meas


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) :
    Measurable (fun t => (fun i j => ((Matrix.of (f t))⁻¹ : Mx k r) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  (B2x1.invM_meas (k := k) (r := r)).comp hf
end Formalism.FourierDecayAlt.P.S3dx4
