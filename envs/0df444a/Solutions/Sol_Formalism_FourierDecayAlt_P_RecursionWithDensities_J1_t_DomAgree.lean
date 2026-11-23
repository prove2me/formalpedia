-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.t_DomAgree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:03.345826+00:00
-- url     : https://prove2.me/submissions/a2e5d55f-0079-4a7f-b143-f278a7121746

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
theorem _root_.solution : DomAgree := by
  intro hAg hTr hTw E W _ _ D T Th hD i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  have hX : TA.PT (fun j s => T.Sg (j - s + 1) s) (i - s) = T.X (i - s) := (hTw E T (i - s)).symm
  refine ⟨fun t ht => ?_, fun t ht t' ht' hl h hh h' hh' => ?_, fun R hR hRd => ?_⟩
  · rw [hX]
    apply ((hAg _ _ _).1).mp
    refine B1.psd_congr (fun x _ y _ => ?_) (hTr _ _ _ (h1 t ht))
    rfl
  · rw [hX] at hh hh'
    exact h2 t ht t' ht' hl h' hh' h hh
  · rw [hX]
    apply ((hAg _ _ _).1).mp
    refine B1.psd_congr (fun x _ y _ => ?_) (hTr _ _ _ (h3 R hR hRd))
    push_cast
    rfl
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
