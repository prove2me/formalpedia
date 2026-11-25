-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.bddClassOpQQ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:07.67899+00:00
-- url     : https://prove2.me/submissions/a0731e53-dd18-46fe-a030-13c0ead567f3

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
theorem _root_.solution (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P)))
    (h : BddClassOp cls) : BddClassOpQQ cls := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun Cc Cb h1 h2 E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    h Cc Cb h1 h2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩
end Formalism.FourierDecayAlt.P.CutMP.JA
