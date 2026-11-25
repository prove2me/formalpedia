-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.measurable_lambda_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:32:28.566338+00:00
-- url     : https://prove2.me/submissions/ae73ff81-c09a-403c-b891-44c07abc0cdb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_measurable_enorm_composition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_hn
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_matmul


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
theorem _root_.solution {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) *
      Matrix.of (Y t))‖ₑ) := by
  have M := meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) hY
  exact measurable_enorm_composition he0 M
end Formalism.FourierDecayAlt.P.S3dx4
