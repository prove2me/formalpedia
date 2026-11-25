-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordKeyIdentity.int_list_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:17.69387+00:00
-- url     : https://prove2.me/submissions/153b8d29-f903-4f4c-b831-cf65a2a29f40

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_WordKeyIdentity_int_list_smul__578b88c14c1d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordKeyIdentity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.WordKeyIdentity
theorem _root_.solution {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum :=
  (int_list_smul' μ l a φ h).2
end Formalism.FourierDecayAlt.P.WordKeyIdentity
