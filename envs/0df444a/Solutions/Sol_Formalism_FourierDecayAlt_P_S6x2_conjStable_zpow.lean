-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.conjStable_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:43.463809+00:00
-- url     : https://prove2.me/submissions/8765c4d4-9623-4246-b13f-6889a3a7d033

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conjStable_pow

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
theorem _root_.solution (A : FI E) (hA0 : A ≠ 0) (hA : ConjStable E A) (n : ℤ) :
    ConjStable E (A ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact conjStable_pow E A hA n
  | negSucc n =>
    rw [zpow_negSucc]
    exact conjStable_inv E _ (pow_ne_zero _ hA0) (conjStable_pow E A hA _)
end Formalism.FourierDecayAlt.P.S6x2
