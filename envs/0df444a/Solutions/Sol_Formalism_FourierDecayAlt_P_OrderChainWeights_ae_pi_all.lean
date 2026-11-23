-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderChainWeights.ae_pi_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:17.846553+00:00
-- url     : https://prove2.me/submissions/37edfffa-2eaf-4f08-ac90-0687b7cd6f8d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderChainWeights
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.OrderChainWeights
theorem _root_.solution {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (i : ℕ)
    (p : X → Prop) (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ h ∂(Measure.pi fun _ : Fin i => μ), ∀ l, p (h l) := by
  rw [ae_all_iff]
  intro l
  exact Measure.tendsto_eval_ae_ae.eventually hp
end Formalism.FourierDecayAlt.P.OrderChainWeights
