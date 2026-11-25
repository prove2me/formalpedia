-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.measurable_lambda_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:00:56.089065+00:00
-- url     : https://prove2.me/submissions/0b21f156-581d-44b0-824b-2c391b7e6ffe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_measurable_lambda_integrand

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
theorem _root_.solution {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => Lam1 e0 μp t.1 t.2) := by
  unfold Lam1
  have m3 := measurable_lambda_integrand he0 (α := (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) (measurable_fst.fst) (measurable_fst.snd) measurable_snd
  exact m3.lintegral_prod_right' (ν := μp)
end Formalism.FourierDecayAlt.P.S3dx4
