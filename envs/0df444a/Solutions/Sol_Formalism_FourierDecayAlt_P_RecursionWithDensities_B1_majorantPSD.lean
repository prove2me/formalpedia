-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.majorantPSD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:44.334564+00:00
-- url     : https://prove2.me/submissions/06fd1356-5785-4f45-8d89-73cc7f4bc84c

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution : MajorantPSD := by
  intro E W _ D T Th hK hD i s hs hsi hi t ht
  have h1 := (hD i s hs hsi hi).1 t ht
  have h2 : TB.PSDOn (T.X (i - s)) (TB.blk (D.Kr i) s t t) := by
    have hY := hK i ((T.X (i - s)).image fun h => join h s t)
    unfold TB.PSDOn at hY ⊢
    have := hY.submatrix (fun h : T.X (i - s) =>
      (⟨join h.1 s t, Finset.mem_image_of_mem _ h.2⟩ : ((T.X (i - s)).image fun h => join h s t)))
    convert this using 1
    ext x y
    rfl
  refine psd_congr ?_ (psd_add h1 h2)
  intro x _ y _
  exact sub_add_cancel _ _
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
