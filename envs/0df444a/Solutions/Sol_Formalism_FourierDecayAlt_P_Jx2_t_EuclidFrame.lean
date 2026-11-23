-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_EuclidFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:14.179871+00:00
-- url     : https://prove2.me/submissions/c023b8e7-89e7-4b40-b635-f554b7d1560e

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_ee_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_eLat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
open NumberField.mixedEmbedding MeasureTheory
open scoped Classical
noncomputable section
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
attribute [local instance] Formalism.FourierDecayAlt.P.Jx2.isEmptyReal
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : EuclidFrame := by
  intro E _ _ _ L c hd hs
  haveI : IsZLattice ℝ (S6.frameLat E L c) := ⟨hs⟩
  rw [eLat_eq E L c]
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · exact IsZLattice.span_top
  · exact ZLattice.covolume_comap _ _ _ (ee_mp E)
end Formalism.FourierDecayAlt.P.Jx2
