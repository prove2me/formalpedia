-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:05.825596+00:00
-- url     : https://prove2.me/submissions/22659baf-cff7-446a-997c-93db686af169

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {α V : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F₁ F₂ : α → V) (c₁ c₂ : ℂ) (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) :
    ∫ x, (c₁ • F₁ x - c₂ • F₂ x) ∂μ = c₁ • ∫ x, F₁ x ∂μ - c₂ • ∫ x, F₂ x ∂μ := by
  have h₁' : Integrable (fun x => c₁ • F₁ x) μ := h₁.smul c₁
  have h₂' : Integrable (fun x => c₂ • F₂ x) μ := h₂.smul c₂
  rw [integral_sub h₁' h₂', integral_smul, integral_smul]
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
