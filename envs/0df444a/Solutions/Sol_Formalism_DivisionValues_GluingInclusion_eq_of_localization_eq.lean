-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.eq_of_localization_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:21.831814+00:00
-- url     : https://prove2.me/submissions/b55b0aa6-c42b-49a5-bb1a-d1f3ae63154b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_le_of_forall_localized_le_of_not_isField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution {D : ℕ} (R R' : Submodule (𝓞 K) (Fin D → K))
    (h : ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal R = localization₂ w.asIdeal R') : R = R' :=
  le_antisymm (le_of_forall_localized_le_of_not_isField (NumberField.RingOfIntegers.not_isField K) R R' fun w => (h w).le)
    (le_of_forall_localized_le_of_not_isField (NumberField.RingOfIntegers.not_isField K) R' R fun w => (h w).ge)
end Formalism.DivisionValues.GluingInclusion
