-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F.pos_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:56.811882+00:00
-- url     : https://prove2.me/submissions/201a8ebf-7bb5-49ec-918b-36507ff6372f

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_A_book_constants_pos_of_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
theorem _root_.solution {P : Type} [Fintype P] (B : S3.MassData P) (h : B.Pos) :
    0 < B.AA ∧ 0 < B.d * B.d' / B.Dstar := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hAA, hD⟩ := Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.book_constants_pos_of_pos B h
  have hd : 0 < B.d := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd' : 0 < B.d' := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨hAA, div_pos (mul_pos hd hd') hD⟩
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
