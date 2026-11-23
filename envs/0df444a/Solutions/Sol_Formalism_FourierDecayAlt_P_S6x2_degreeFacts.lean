-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.degreeFacts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:45.15321+00:00
-- url     : https://prove2.me/submissions/f96bce3b-f9db-493e-b181-facdd7f2cdf4

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
theorem _root_.solution : DegreeFacts := by
  intro E _ _ _
  have h2 : finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h4 : 0 < finrank ℚ (maximalRealSubfield E) := finrank_pos
  rw [h2] at h3
  refine ⟨by unfold deg; omega, ?_, h4⟩
  have h5 := IsTotallyComplex.finrank E
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  unfold deg
  omega
end Formalism.FourierDecayAlt.P.S6x2
