-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.conjStable_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:45.113369+00:00
-- url     : https://prove2.me/submissions/5932520b-56a7-4b49-832e-bd7e9665c521

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (A B : FI E) (hA : ConjStable E A) (hB : ConjStable E B) :
    ConjStable E (A * B) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on (C := fun x => complexConj E x ∈ A * B) hx
    (fun i hi j hj => ?_) (fun x y hx hy => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hA i hi) (hB j hj)
  · rw [map_add]; exact (A * B).coeToSubmodule.add_mem hx hy
end Formalism.FourierDecayAlt.P.S6x2
