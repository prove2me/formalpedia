-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.jABddOpQQ_of_jABddOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:45:49.957807+00:00
-- url     : https://prove2.me/submissions/367c8979-40ea-4297-bc5e-92745626ae75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
open NumberField Formalism.FourierDecayAlt.P.CutMP
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.JA
theorem _root_.solution (h : JABddOp) : JABddOpQQ := by
  obtain ⟨Cc, Cb, hCb, h⟩ := h
  exact ⟨Cc, Cb, hCb, fun E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    h E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩
end Formalism.FourierDecayAlt.P.CutMP.JA
