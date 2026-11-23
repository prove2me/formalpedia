-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.coordU_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:53.547253+00:00
-- url     : https://prove2.me/submissions/e7d08819-d9a6-4f32-b786-8a0a07417e21

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
theorem _root_.solution {d : ℕ} (v : UT d → ℂ) : coordU (upper v) = v := by
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  have h' : i < j := h
  simp [coordU, upper, strictUpper, h', h'.ne]
end Formalism.FourierDecayAlt.P.G5
