-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.ee_cemb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:22.608801+00:00
-- url     : https://prove2.me/submissions/65a486ca-403d-42b7-a598-eaef6341fcf2

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean

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
theorem _root_.solution (t : E) : ee E (cemb E t) = mixedEmbedding E t := by
  ext w
  · exact isEmptyElim w
  · rfl
end Formalism.FourierDecayAlt.P.Jx2
