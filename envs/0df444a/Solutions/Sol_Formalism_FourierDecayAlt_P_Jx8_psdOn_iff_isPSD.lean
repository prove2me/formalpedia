-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.psdOn_iff_isPSD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:38.640805+00:00
-- url     : https://prove2.me/submissions/9bb5978c-2ad4-4acf-9772-bc7505daaafc

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_tb_iff_ta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_isPSD_iff_psdOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) : TB.PSDOn F k ↔ A5.IsPSD F k :=
  (tb_iff_ta F k).trans (isPSD_iff_psdOn F k).symm
end Formalism.FourierDecayAlt.P.Jx8
