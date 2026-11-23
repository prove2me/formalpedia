-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.pos_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:51.544238+00:00
-- url     : https://prove2.me/submissions/ab360aa6-9c28-4800-a17d-d0bc5633c20c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_ofReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution {a b : ℂ} (ha : Pos a) (hb : Pos b) : Pos (a / b) := by
  rw [pos_eq ha, pos_eq hb, ← Complex.ofReal_div]
  exact pos_ofReal (div_pos ha.1 hb.1)
end Formalism.FourierDecayAlt.P.Fr2
