-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.conjStable_dd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:50.443298+00:00
-- url     : https://prove2.me/submissions/a58bd5bb-90bc-4b13-a512-998e053932f7

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_trace_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dd_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dual_one

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
theorem _root_.solution : ConjStable E (dd E) := by
  have h : ConjStable E (dd E)⁻¹ := by
    rw [← dual_one]
    intro x hx
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)] at hx ⊢
    intro a ha
    have := hx _ (conjStable_one E a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← trace_conj, map_mul, complexConj_apply_apply] at this
    exact this
  have := conjStable_inv E _ (inv_ne_zero (dd_ne_zero E)) h
  rwa [inv_inv] at this
end Formalism.FourierDecayAlt.P.S6x2
