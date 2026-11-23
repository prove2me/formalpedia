-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:05.355357+00:00
-- url     : https://prove2.me/submissions/e972b7ce-0bb5-482e-ac8b-91246a923e93

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure α} {μ : Measure β} {μ' : Measure γ} {J : α → β} {F : β → γ}
    (hJ : MeasurePreserving J ν μ) (hF : Measurable F) (h : MeasurePreserving (F ∘ J) ν μ') :
    MeasurePreserving F μ μ' :=
  ⟨hF, by rw [← hJ.map_eq, Measure.map_map hF hJ.measurable]; exact h.map_eq⟩
end Formalism.FourierDecayAlt.P.G5
