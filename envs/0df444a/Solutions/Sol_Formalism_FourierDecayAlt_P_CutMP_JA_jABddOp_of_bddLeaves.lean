-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.jABddOp_of_bddLeaves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:53:41.228974+00:00
-- url     : https://prove2.me/submissions/635224d1-c5eb-439d-8381-0ca26e0cf3bd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddOp
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_bddSet_cases

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
theorem _root_.solution (h1 : JABddScal) (h2 : JABddKap) (h3 : JABddSSn) (h4 : JABddSSnStar) : JABddOp := by
  obtain ⟨K1, hK1, h1⟩ := h1
  obtain ⟨K2, hK2, h2⟩ := h2
  obtain ⟨K3, hK3, h3⟩ := h3
  obtain ⟨K4, hK4, h4⟩ := h4
  set K := max (max K1 K2) (max K3 K4) with hK
  have e1 : K1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : K2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : K3 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : K4 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨K, K, le_trans hK1 e1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL b hb
  rcases bddSet_cases _ L b hb with h | h | h | h
  · exact h1 K K e1 e1 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL b h
  · exact h2 K K e2 e2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL b h
  · exact h3 K K e3 e3 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL b h
  · exact h4 K K e4 e4 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL b h
end Formalism.FourierDecayAlt.P.CutMP.JA
