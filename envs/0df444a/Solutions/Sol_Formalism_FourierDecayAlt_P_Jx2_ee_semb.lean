-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.ee_semb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:14.889204+00:00
-- url     : https://prove2.me/submissions/c21340da-073f-4917-a342-06983ae2207f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_ee_cemb

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
theorem _root_.solution (c : ℝ) (t : E) : ee E (semb E c t) = c • mixedEmbedding E t := by
  have h : semb E c t = c • cemb E t := rfl
  rw [h, map_smul, ee_cemb]
end Formalism.FourierDecayAlt.P.Jx2
