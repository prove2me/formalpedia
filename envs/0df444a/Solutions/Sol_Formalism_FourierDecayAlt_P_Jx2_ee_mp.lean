-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.ee_mp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:38.484329+00:00
-- url     : https://prove2.me/submissions/f732b428-2305-4778-ac52-445444b7f9c7

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
theorem _root_.solution : MeasurePreserving (ee E) := by
  have h : ⇑(ee E) = ⇑(euclidean.toMixed E) ∘ ⇑(phi E) := rfl
  rw [h]
  first
  | exact (euclidean.volumePreserving_toMixed E).comp (phi E).measurePreserving
  | exact euclidean.volumePreserving_toMixed.comp (phi E).measurePreserving
  | exact (euclidean.volumePreserving_toMixed E).comp (LinearIsometryEquiv.measurePreserving (phi E))
end Formalism.FourierDecayAlt.P.Jx2
