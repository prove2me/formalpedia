-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.majorantPSDA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:07.260158+00:00
-- url     : https://prove2.me/submissions/5dadb5d1-fce4-465c-aa00-2c83aa58e479

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_blk_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution : TC.MajorantPSDA := by
  intro E _ _ D Sg Th hNZ hK hD i s hs hsi hi t ht
  have h1 := (hD i s hs hsi hi).1 t ht
  have h2 := blk_psd D Sg hNZ hK i s hs hsi hi t (hNZ i s t ht)
  refine psd_congr ?_ (psd_add h1 h2)
  intro x _ y _
  exact sub_add_cancel _ _
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
