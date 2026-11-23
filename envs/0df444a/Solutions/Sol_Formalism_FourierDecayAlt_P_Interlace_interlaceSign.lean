-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.interlaceSign
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.01789+00:00
-- url     : https://prove2.me/submissions/cb24bd2a-d2e1-4490-8fa8-4b767306243d

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_sign_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I
namespace Formalism.FourierDecayAlt.P.Interlace
theorem _root_.solution : InterlaceSign := by
  intro k u u' ρ l Y hl1 hlk h hc e he
  have he' : -1 ≤ e ∧ e ≤ 1 := by
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  rcases hc with hA | hB
  · exact sign_core k u u' ρ l Y hl1 hlk h hA e he'
  · exact sign_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB e he'
end Formalism.FourierDecayAlt.P.Interlace
